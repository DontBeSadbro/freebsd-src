/*-
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright (c) 2002-2006 Rice University
 * Copyright (c) 2007 Alan L. Cox <alc@cs.rice.edu>
 * All rights reserved.
 *
 * This software was developed for the FreeBSD Project by Alan L. Cox,
 * Olivier Crameri, Peter Druschel, Sitaram Iyer, and Juan Navarro.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT
 * HOLDERS OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS
 * OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED
 * AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY
 * WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

/*
 *	Physical memory system implementation
 *
 * Any external functions defined by this module are only to be used by the
 * virtual memory system.
 */

#include <sys/cdefs.h>
__FBSDID("$FreeBSD$");

#include "opt_ddb.h"
#include "opt_vm.h"

#include <sys/param.h>
#include <sys/systm.h>
#include <sys/domainset.h>
#include <sys/kernel.h>
#include <sys/lock.h>
#include <sys/malloc.h>
#include <sys/mutex.h>
#include <sys/proc.h>
#include <sys/queue.h>
#include <sys/rwlock.h>
#include <sys/sbuf.h>
#include <sys/sysctl.h>
#include <sys/tree.h>
#include <sys/vmmeter.h>
#include <sys/kthread.h>
#include <sys/eventhandler.h>
#include <sys/sdt.h>


#include <vm/vm.h>
#include <vm/vm_compact.h>
#include <vm/vm_extern.h>
#include <vm/vm_kern.h>
#include <vm/vm_object.h>
#include <vm/vm_page.h>
#include <vm/vm_pagequeue.h>
#include <vm/vm_param.h>
#include <vm/vm_phys.h>

#include <ddb/ddb.h>

_Static_assert(sizeof(long) * NBBY >= VM_PHYSSEG_MAX,
    "Too many physsegs.");

#ifdef NUMA
struct mem_affinity __read_mostly *mem_affinity;
int __read_mostly *mem_locality;
#endif

int __read_mostly vm_ndomains = 1;
domainset_t __read_mostly all_domains = DOMAINSET_T_INITIALIZER(0x1);

struct vm_phys_seg __read_mostly vm_phys_segs[VM_PHYSSEG_MAX];
int __read_mostly vm_phys_nsegs;
static struct vm_phys_seg vm_phys_early_segs[8];
static int vm_phys_early_nsegs;

struct vm_phys_fictitious_seg;
static int vm_phys_fictitious_cmp(struct vm_phys_fictitious_seg *,
    struct vm_phys_fictitious_seg *);

RB_HEAD(fict_tree, vm_phys_fictitious_seg) vm_phys_fictitious_tree =
    RB_INITIALIZER(&vm_phys_fictitious_tree);

struct vm_phys_fictitious_seg {
	RB_ENTRY(vm_phys_fictitious_seg) node;
	/* Memory region data */
	vm_paddr_t	start;
	vm_paddr_t	end;
	vm_page_t	first_page;
};

RB_GENERATE_STATIC(fict_tree, vm_phys_fictitious_seg, node,
    vm_phys_fictitious_cmp);

static struct rwlock_padalign vm_phys_fictitious_reg_lock;
MALLOC_DEFINE(M_FICT_PAGES, "vm_fictitious", "Fictitious VM pages");

struct vm_phys_hole {
	/* Memory hole region data */
	vm_paddr_t start;
	vm_paddr_t end;
	int domain;
};
/*  */
static struct vm_phys_hole vm_phys_holes[VM_PHYSSEG_MAX];
static int vm_phys_nholes;

static void vm_phys_update_search_index(vm_page_t m, int order, bool alloc);

static struct vm_freelist __aligned(CACHE_LINE_SIZE)
    vm_phys_free_queues[MAXMEMDOM][VM_NFREELIST][VM_NFREEPOOL]
    [VM_NFREEORDER_MAX];

static int __read_mostly vm_nfreelists;

/*
 * These "avail lists" are globals used to communicate boot-time physical
 * memory layout to other parts of the kernel.  Each physically contiguous
 * region of memory is defined by a start address at an even index and an
 * end address at the following odd index.  Each list is terminated by a
 * pair of zero entries.
 *
 * dump_avail tells the dump code what regions to include in a crash dump, and
 * phys_avail is all of the remaining physical memory that is available for
 * the vm system.
 *
 * Initially dump_avail and phys_avail are identical.  Boot time memory
 * allocations remove extents from phys_avail that may still be included
 * in dumps.
 */
vm_paddr_t phys_avail[PHYS_AVAIL_COUNT];
vm_paddr_t dump_avail[PHYS_AVAIL_COUNT];

struct vm_phys_info {
        uint64_t free_pages;
        uint64_t free_blocks;
        uint64_t order_suitable_pages;
};

/*
 * Provides the mapping from VM_FREELIST_* to free list indices (flind).
 */
static int __read_mostly vm_freelist_to_flind[VM_NFREELIST];

CTASSERT(VM_FREELIST_DEFAULT == 0);

#ifdef VM_FREELIST_DMA32
#define	VM_DMA32_BOUNDARY	((vm_paddr_t)1 << 32)
#endif

/*
 * Enforce the assumptions made by vm_phys_add_seg() and vm_phys_init() about
 * the ordering of the free list boundaries.
 */
#if defined(VM_LOWMEM_BOUNDARY) && defined(VM_DMA32_BOUNDARY)
CTASSERT(VM_LOWMEM_BOUNDARY < VM_DMA32_BOUNDARY);
#endif

static int sysctl_vm_phys_free(SYSCTL_HANDLER_ARGS);
SYSCTL_OID(_vm, OID_AUTO, phys_free,
    CTLTYPE_STRING | CTLFLAG_RD | CTLFLAG_MPSAFE, NULL, 0,
    sysctl_vm_phys_free, "A",
    "Phys Free Info");

static int sysctl_vm_phys_frag_idx(SYSCTL_HANDLER_ARGS);
SYSCTL_OID(_vm, OID_AUTO, phys_frag_idx,
    CTLTYPE_STRING | CTLFLAG_RD | CTLFLAG_MPSAFE, NULL, 0,
    sysctl_vm_phys_frag_idx, "A",
    "Phys Frag Info");

static int sysctl_vm_phys_unusable_idx(SYSCTL_HANDLER_ARGS);
SYSCTL_OID(_vm, OID_AUTO, phys_unusable_idx,
    CTLTYPE_STRING | CTLFLAG_RD | CTLFLAG_MPSAFE, NULL, 0,
    sysctl_vm_phys_unusable_idx, "A",
    "Phys Unusable Idx Info");

static int sysctl_vm_phys_segs(SYSCTL_HANDLER_ARGS);
SYSCTL_OID(_vm, OID_AUTO, phys_segs,
    CTLTYPE_STRING | CTLFLAG_RD | CTLFLAG_MPSAFE, NULL, 0,
    sysctl_vm_phys_segs, "A",
    "Phys Seg Info");

#ifdef NUMA
static int sysctl_vm_phys_locality(SYSCTL_HANDLER_ARGS);
SYSCTL_OID(_vm, OID_AUTO, phys_locality,
    CTLTYPE_STRING | CTLFLAG_RD | CTLFLAG_MPSAFE, NULL, 0,
    sysctl_vm_phys_locality, "A",
    "Phys Locality Info");
#endif

SYSCTL_INT(_vm, OID_AUTO, ndomains, CTLFLAG_RD,
    &vm_ndomains, 0, "Number of physical memory domains available.");

static void _vm_phys_create_seg(vm_paddr_t start, vm_paddr_t end, int domain);
static void vm_phys_create_seg(vm_paddr_t start, vm_paddr_t end);
static void vm_phys_split_pages(vm_page_t m, int oind, struct vm_freelist *fl,
    int order, int tail);

/*
 * Red-black tree helpers for vm fictitious range management.
 */
static inline int
vm_phys_fictitious_in_range(struct vm_phys_fictitious_seg *p,
    struct vm_phys_fictitious_seg *range)
{

	KASSERT(range->start != 0 && range->end != 0,
	    ("Invalid range passed on search for vm_fictitious page"));
	if (p->start >= range->end)
		return (1);
	if (p->start < range->start)
		return (-1);

	return (0);
}

static int
vm_phys_fictitious_cmp(struct vm_phys_fictitious_seg *p1,
    struct vm_phys_fictitious_seg *p2)
{

	/* Check if this is a search for a page */
	if (p1->end == 0)
		return (vm_phys_fictitious_in_range(p1, p2));

	KASSERT(p2->end != 0,
    ("Invalid range passed as second parameter to vm fictitious comparison"));

	/* Searching to add a new range */
	if (p1->end <= p2->start)
		return (-1);
	if (p1->start >= p2->end)
		return (1);

	panic("Trying to add overlapping vm fictitious ranges:\n"
	    "[%#jx:%#jx] and [%#jx:%#jx]", (uintmax_t)p1->start,
	    (uintmax_t)p1->end, (uintmax_t)p2->start, (uintmax_t)p2->end);
}

int
vm_phys_domain_match(int prefer, vm_paddr_t low, vm_paddr_t high)
{
#ifdef NUMA
	domainset_t mask;
	int i;

	if (vm_ndomains == 1 || mem_affinity == NULL)
		return (0);

	DOMAINSET_ZERO(&mask);
	/*
	 * Check for any memory that overlaps low, high.
	 */
	for (i = 0; mem_affinity[i].end != 0; i++)
		if (mem_affinity[i].start <= high &&
		    mem_affinity[i].end >= low)
			DOMAINSET_SET(mem_affinity[i].domain, &mask);
	if (prefer != -1 && DOMAINSET_ISSET(prefer, &mask))
		return (prefer);
	if (DOMAINSET_EMPTY(&mask))
		panic("vm_phys_domain_match:  Impossible constraint");
	return (DOMAINSET_FFS(&mask) - 1);
#else
	return (0);
#endif
}

/*
 * Outputs the state of the physical memory allocator, specifically,
 * the amount of physical memory in each free list.
 */
static int
sysctl_vm_phys_free(SYSCTL_HANDLER_ARGS)
{
	struct sbuf sbuf;
	struct vm_freelist *fl;
	int dom, error, flind, oind, pind;

	error = sysctl_wire_old_buffer(req, 0);
	if (error != 0)
		return (error);
	sbuf_new_for_sysctl(&sbuf, NULL, 128 * vm_ndomains, req);
	for (dom = 0; dom < vm_ndomains; dom++) {
		sbuf_printf(&sbuf,"\nDOMAIN %d:\n", dom);
		for (flind = 0; flind < vm_nfreelists; flind++) {
			sbuf_printf(&sbuf, "\nFREE LIST %d:\n"
			    "\n  ORDER (SIZE)  |  NUMBER"
			    "\n              ", flind);
			for (pind = 0; pind < VM_NFREEPOOL; pind++)
				sbuf_printf(&sbuf, "  |  POOL %d", pind);
			sbuf_printf(&sbuf, "\n--            ");
			for (pind = 0; pind < VM_NFREEPOOL; pind++)
				sbuf_printf(&sbuf, "-- --      ");
			sbuf_printf(&sbuf, "--\n");
			for (oind = VM_NFREEORDER - 1; oind >= 0; oind--) {
				sbuf_printf(&sbuf, "  %2d (%6dK)", oind,
				    1 << (PAGE_SHIFT - 10 + oind));
				for (pind = 0; pind < VM_NFREEPOOL; pind++) {
				fl = vm_phys_free_queues[dom][flind][pind];
					sbuf_printf(&sbuf, "  |  %6d",
					    fl[oind].lcnt);
				}
				sbuf_printf(&sbuf, "\n");
			}
		}
	}
	error = sbuf_finish(&sbuf);
	sbuf_delete(&sbuf);
	return (error);
}

static void
vm_phys_get_info(struct vm_phys_info *info, int domain)
{
        struct vm_freelist *fl;
	int pind, oind, flind;

	/* Calculate total number of free pages and blocks */
        info->free_pages = info->order_suitable_pages = info->free_blocks = 0;
	for (flind = 0; flind < vm_nfreelists; flind++) {
		for (oind = VM_NFREEORDER - 1; oind >= 0; oind--) {
			for (pind = 0; pind < VM_NFREEPOOL; pind++) {
				fl = vm_phys_free_queues[domain][flind][pind];
				info->free_pages += fl[oind].lcnt << oind;
				info->free_blocks += fl[oind].lcnt;
			}
		}
	}
}

static void
vm_phys_get_order_info(struct vm_phys_info *info, int order, int domain)
{
        struct vm_freelist *fl;
	int pind, oind, flind;

	/* Calculate total number of free pages
           for the specified order and higher orders */
        info->order_suitable_pages = 0;
        for (oind = VM_NFREEORDER - 1; oind >= order; oind--) {
                        for (flind = 0; flind < vm_nfreelists; flind++) {
                                for (pind = 0; pind < VM_NFREEPOOL; pind++) {
					fl = vm_phys_free_queues[domain][flind]
								[pind];
					info->order_suitable_pages += fl[oind].lcnt << oind;
                                }
                        }
        }
}

int
vm_phys_fragmentation_index(int order, int domain)
{
        struct vm_phys_info info;

	vm_domain_free_assert_locked(VM_DOMAIN(domain));
	vm_phys_get_info(&info, domain);

  if(info.free_blocks == 0){
    return (0);
  }

	return (1000 -
                                 ((info.free_pages * 1000) / (1 << order) / info.free_blocks));
}

static int
vm_phys_unusable_index(int order, int domain)
{
        struct vm_phys_info info;

	vm_domain_free_assert_locked(VM_DOMAIN(domain));
	vm_phys_get_info(&info, domain);
	vm_phys_get_order_info(&info, order, domain);

	return (((info.free_pages - info.order_suitable_pages) * 1000) /
	    info.free_pages);
}

/*
 * Outputs the value of the Free Memory Fragmentation Index (FMFI) for each
 * domain.
 */
static int
sysctl_vm_phys_frag_idx(SYSCTL_HANDLER_ARGS)
{
	struct sbuf sbuf;
  int64_t idx;
  int oind, dom, error;

  error = sysctl_wire_old_buffer(req, 0);
	if (error != 0)
          return (error);
	sbuf_new_for_sysctl(&sbuf, NULL, 128 * vm_ndomains, req);

	for (dom = 0; dom < vm_ndomains; dom++) {
		vm_domain_free_lock(VM_DOMAIN(dom));

		sbuf_printf(&sbuf, "\n--\n");
		sbuf_printf(&sbuf, "\nDOMAIN %d\n", dom);
		sbuf_printf(&sbuf, "\n  ORDER (SIZE) |  FMFI\n");
		sbuf_printf(&sbuf, "--\n");

		for (oind = VM_NFREEORDER - 1; oind >= 0; oind--) {
			idx = vm_phys_fragmentation_index(oind, dom);
			sbuf_printf(&sbuf, "  %2d (%6dK) ", oind,
			    1 << (PAGE_SHIFT - 10 + oind));
			sbuf_printf(&sbuf, "|  %ld \n", idx);
		}

		vm_domain_free_unlock(VM_DOMAIN(dom));
	}

	error = sbuf_finish(&sbuf);
	sbuf_delete(&sbuf);
	return (error);
}

/*
 * Outputs the value of the unusable free space index for each domain.
 */
static int
sysctl_vm_phys_unusable_idx(SYSCTL_HANDLER_ARGS)
{
	struct sbuf sbuf;
	int oind, dom, error;
	int64_t idx;

	error = sysctl_wire_old_buffer(req, 0);
	if (error != 0)
          return (error);
	sbuf_new_for_sysctl(&sbuf, NULL, 128 * vm_ndomains, req);

	for (dom = 0; dom < vm_ndomains; dom++) {
		vm_domain_free_lock(VM_DOMAIN(dom));

		sbuf_printf(&sbuf, "\n--\n");
		sbuf_printf(&sbuf, "DOMAIN %d\n", dom);
		sbuf_printf(&sbuf, "\n  ORDER (SIZE) |  UFSI\n");
		sbuf_printf(&sbuf, "--\n");

		for (oind = VM_NFREEORDER - 1; oind >= 0; oind--) {
			idx = vm_phys_unusable_index(oind, dom);
			sbuf_printf(&sbuf, "  %2d (%6dK) ", oind,
			    1 << (PAGE_SHIFT - 10 + oind));
			sbuf_printf(&sbuf, "|  %ld \n", idx);
		}

		vm_domain_free_unlock(VM_DOMAIN(dom));
	}

	error = sbuf_finish(&sbuf);
	sbuf_delete(&sbuf);
	return (error);
}

/*
 * Outputs the set of physical memory segments.
 */
static int
sysctl_vm_phys_segs(SYSCTL_HANDLER_ARGS)
{
	struct sbuf sbuf;
	struct vm_phys_seg *seg;
	int error, segind;

	error = sysctl_wire_old_buffer(req, 0);
	if (error != 0)
		return (error);
	sbuf_new_for_sysctl(&sbuf, NULL, 128, req);
	for (segind = 0; segind < vm_phys_nsegs; segind++) {
		sbuf_printf(&sbuf, "\nSEGMENT %d:\n\n", segind);
		seg = &vm_phys_segs[segind];
		sbuf_printf(&sbuf, "start:     %#jx\n",
		    (uintmax_t)seg->start);
		sbuf_printf(&sbuf, "end:       %#jx\n",
		    (uintmax_t)seg->end);
		sbuf_printf(&sbuf, "domain:    %d\n", seg->domain);
		sbuf_printf(&sbuf, "free list: %p\n", seg->free_queues);
	}
	error = sbuf_finish(&sbuf);
	sbuf_delete(&sbuf);
	return (error);
}

/*
 * Return affinity, or -1 if there's no affinity information.
 */
int
vm_phys_mem_affinity(int f, int t)
{

#ifdef NUMA
	if (mem_locality == NULL)
		return (-1);
	if (f >= vm_ndomains || t >= vm_ndomains)
		return (-1);
	return (mem_locality[f * vm_ndomains + t]);
#else
	return (-1);
#endif
}

#ifdef NUMA
/*
 * Outputs the VM locality table.
 */
static int
sysctl_vm_phys_locality(SYSCTL_HANDLER_ARGS)
{
	struct sbuf sbuf;
	int error, i, j;

	error = sysctl_wire_old_buffer(req, 0);
	if (error != 0)
		return (error);
	sbuf_new_for_sysctl(&sbuf, NULL, 128, req);

	sbuf_printf(&sbuf, "\n");

	for (i = 0; i < vm_ndomains; i++) {
		sbuf_printf(&sbuf, "%d: ", i);
		for (j = 0; j < vm_ndomains; j++) {
			sbuf_printf(&sbuf, "%d ", vm_phys_mem_affinity(i, j));
		}
		sbuf_printf(&sbuf, "\n");
	}
	error = sbuf_finish(&sbuf);
	sbuf_delete(&sbuf);
	return (error);
}
#endif

static void
vm_freelist_add(struct vm_freelist *fl, vm_page_t m, int order, int tail)
{

	m->order = order;
	if (tail)
		TAILQ_INSERT_TAIL(&fl[order].pl, m, listq);
	else
		TAILQ_INSERT_HEAD(&fl[order].pl, m, listq);
	fl[order].lcnt++;
	vm_phys_update_search_index(m, order, false);
}

static void
vm_freelist_rem(struct vm_freelist *fl, vm_page_t m, int order)
{

	TAILQ_REMOVE(&fl[order].pl, m, listq);
	fl[order].lcnt--;
	m->order = VM_NFREEORDER;
	vm_phys_update_search_index(m, order, true);
}

/*
 * Create a physical memory segment.
 */
static void
_vm_phys_create_seg(vm_paddr_t start, vm_paddr_t end, int domain)
{
	struct vm_phys_seg *seg;

	KASSERT(vm_phys_nsegs < VM_PHYSSEG_MAX,
	    ("vm_phys_create_seg: increase VM_PHYSSEG_MAX"));
	KASSERT(domain >= 0 && domain < vm_ndomains,
	    ("vm_phys_create_seg: invalid domain provided"));
	seg = &vm_phys_segs[vm_phys_nsegs++];
	while (seg > vm_phys_segs && (seg - 1)->start >= end) {
		*seg = *(seg - 1);
		seg--;
	}
	seg->start = start;
	seg->end = end;
	seg->domain = domain;
}

static void
vm_phys_create_seg(vm_paddr_t start, vm_paddr_t end)
{
#ifdef NUMA
	int i;

	if (mem_affinity == NULL) {
		_vm_phys_create_seg(start, end, 0);
		return;
	}

	for (i = 0;; i++) {
		if (mem_affinity[i].end == 0)
			panic("Reached end of affinity info");
		if (mem_affinity[i].end <= start)
			continue;
		if (mem_affinity[i].start > start)
			panic("No affinity info for start %jx",
			    (uintmax_t)start);
		if (mem_affinity[i].end >= end) {
			_vm_phys_create_seg(start, end,
			    mem_affinity[i].domain);
			break;
		}
		_vm_phys_create_seg(start, mem_affinity[i].end,
		    mem_affinity[i].domain);
		start = mem_affinity[i].end;
	}
#else
	_vm_phys_create_seg(start, end, 0);
#endif
}

/*
 * Add a physical memory segment.
 */
void
vm_phys_add_seg(vm_paddr_t start, vm_paddr_t end)
{
	vm_paddr_t paddr;

	KASSERT((start & PAGE_MASK) == 0,
	    ("vm_phys_define_seg: start is not page aligned"));
	KASSERT((end & PAGE_MASK) == 0,
	    ("vm_phys_define_seg: end is not page aligned"));

	/*
	 * Split the physical memory segment if it spans two or more free
	 * list boundaries.
	 */
	paddr = start;
#ifdef	VM_FREELIST_LOWMEM
	if (paddr < VM_LOWMEM_BOUNDARY && end > VM_LOWMEM_BOUNDARY) {
		vm_phys_create_seg(paddr, VM_LOWMEM_BOUNDARY);
		paddr = VM_LOWMEM_BOUNDARY;
	}
#endif
#ifdef	VM_FREELIST_DMA32
	if (paddr < VM_DMA32_BOUNDARY && end > VM_DMA32_BOUNDARY) {
		vm_phys_create_seg(paddr, VM_DMA32_BOUNDARY);
		paddr = VM_DMA32_BOUNDARY;
	}
#endif
	vm_phys_create_seg(paddr, end);
}

/*
 * Initialize the physical memory allocator.
 *
 * Requires that vm_page_array is initialized!
 */
void
vm_phys_init(void)
{
	struct vm_freelist *fl;
	struct vm_phys_seg *end_seg, *prev_seg, *seg, *tmp_seg;
#if defined(VM_DMA32_NPAGES_THRESHOLD) || defined(VM_PHYSSEG_SPARSE)
	u_long npages;
#endif
	int dom, flind, freelist, oind, pind, segind;

	/*
	 * Compute the number of free lists, and generate the mapping from the
	 * manifest constants VM_FREELIST_* to the free list indices.
	 *
	 * Initially, the entries of vm_freelist_to_flind[] are set to either
	 * 0 or 1 to indicate which free lists should be created.
	 */
#ifdef	VM_DMA32_NPAGES_THRESHOLD
	npages = 0;
#endif
	for (segind = vm_phys_nsegs - 1; segind >= 0; segind--) {
		seg = &vm_phys_segs[segind];
#ifdef	VM_FREELIST_LOWMEM
		if (seg->end <= VM_LOWMEM_BOUNDARY)
			vm_freelist_to_flind[VM_FREELIST_LOWMEM] = 1;
		else
#endif
#ifdef	VM_FREELIST_DMA32
		if (
#ifdef	VM_DMA32_NPAGES_THRESHOLD
		    /*
		     * Create the DMA32 free list only if the amount of
		     * physical memory above physical address 4G exceeds the
		     * given threshold.
		     */
		    npages > VM_DMA32_NPAGES_THRESHOLD &&
#endif
		    seg->end <= VM_DMA32_BOUNDARY)
			vm_freelist_to_flind[VM_FREELIST_DMA32] = 1;
		else
#endif
		{
#ifdef	VM_DMA32_NPAGES_THRESHOLD
			npages += atop(seg->end - seg->start);
#endif
			vm_freelist_to_flind[VM_FREELIST_DEFAULT] = 1;
		}
	}
	/* Change each entry into a running total of the free lists. */
	for (freelist = 1; freelist < VM_NFREELIST; freelist++) {
		vm_freelist_to_flind[freelist] +=
		    vm_freelist_to_flind[freelist - 1];
	}
	vm_nfreelists = vm_freelist_to_flind[VM_NFREELIST - 1];
	KASSERT(vm_nfreelists > 0, ("vm_phys_init: no free lists"));
	/* Change each entry into a free list index. */
	for (freelist = 0; freelist < VM_NFREELIST; freelist++)
		vm_freelist_to_flind[freelist]--;

	/*
	 * Initialize the first_page and free_queues fields of each physical
	 * memory segment.
	 */
#ifdef VM_PHYSSEG_SPARSE
	npages = 0;
#endif
	for (segind = 0; segind < vm_phys_nsegs; segind++) {
		seg = &vm_phys_segs[segind];
#ifdef VM_PHYSSEG_SPARSE
		seg->first_page = &vm_page_array[npages];
		npages += atop(seg->end - seg->start);
#else
		seg->first_page = PHYS_TO_VM_PAGE(seg->start);
#endif
#ifdef	VM_FREELIST_LOWMEM
		if (seg->end <= VM_LOWMEM_BOUNDARY) {
			flind = vm_freelist_to_flind[VM_FREELIST_LOWMEM];
			KASSERT(flind >= 0,
			    ("vm_phys_init: LOWMEM flind < 0"));
		} else
#endif
#ifdef	VM_FREELIST_DMA32
		if (seg->end <= VM_DMA32_BOUNDARY) {
			flind = vm_freelist_to_flind[VM_FREELIST_DMA32];
			KASSERT(flind >= 0,
			    ("vm_phys_init: DMA32 flind < 0"));
		} else
#endif
		{
			flind = vm_freelist_to_flind[VM_FREELIST_DEFAULT];
			KASSERT(flind >= 0,
			    ("vm_phys_init: DEFAULT flind < 0"));
		}
		seg->free_queues = &vm_phys_free_queues[seg->domain][flind];
	}

	/*
	 * Coalesce physical memory segments that are contiguous and share the
	 * same per-domain free queues.
	 */
	prev_seg = vm_phys_segs;
	seg = &vm_phys_segs[1];
	end_seg = &vm_phys_segs[vm_phys_nsegs];
	while (seg < end_seg) {
		if (prev_seg->end == seg->start &&
		    prev_seg->free_queues == seg->free_queues) {
			prev_seg->end = seg->end;
			KASSERT(prev_seg->domain == seg->domain,
			    ("vm_phys_init: free queues cannot span domains"));
			vm_phys_nsegs--;
			end_seg--;
			for (tmp_seg = seg; tmp_seg < end_seg; tmp_seg++)
				*tmp_seg = *(tmp_seg + 1);
		} else {
			prev_seg = seg;
			seg++;
		}
	}

	/*
	 * Initialize the free queues.
	 */
	for (dom = 0; dom < vm_ndomains; dom++) {
		for (flind = 0; flind < vm_nfreelists; flind++) {
			for (pind = 0; pind < VM_NFREEPOOL; pind++) {
				fl = vm_phys_free_queues[dom][flind][pind];
				for (oind = 0; oind < VM_NFREEORDER; oind++)
					TAILQ_INIT(&fl[oind].pl);
			}
		}
	}

	/*
	 * Initialize hole array.
	 */
	struct vm_phys_hole *hp;

	vm_phys_nholes = 0;
	if (vm_phys_segs[0].start != 0) {
		hp = &vm_phys_holes[0];
		hp->start = 0;
		hp->end = vm_phys_segs[0].start;
		hp->domain = vm_phys_segs[0].domain;
		vm_phys_nholes++;
	}

	for (int i = 0; i < (vm_phys_nsegs - 1); i++, vm_phys_nholes++) {
		hp = &vm_phys_holes[vm_phys_nholes];
		hp->start = vm_phys_segs[i].end;
		hp->end = vm_phys_segs[i + 1].start;
		hp->domain = vm_phys_segs[i].domain;
	}

	rw_init(&vm_phys_fictitious_reg_lock, "vmfctr");
}

/*
 * Register info about the NUMA topology of the system.
 *
 * Invoked by platform-dependent code prior to vm_phys_init().
 */
void
vm_phys_register_domains(int ndomains, struct mem_affinity *affinity,
    int *locality)
{
#ifdef NUMA
	int d, i;

	/*
	 * For now the only override value that we support is 1, which
	 * effectively disables NUMA-awareness in the allocators.
	 */
	d = 0;
	TUNABLE_INT_FETCH("vm.numa.disabled", &d);
	if (d)
		ndomains = 1;

	if (ndomains > 1) {
		vm_ndomains = ndomains;
		mem_affinity = affinity;
		mem_locality = locality;
	}

	for (i = 0; i < vm_ndomains; i++)
		DOMAINSET_SET(i, &all_domains);
#else
	(void)ndomains;
	(void)affinity;
	(void)locality;
#endif
}

/*
 * Split a contiguous, power of two-sized set of physical pages.
 *
 * When this function is called by a page allocation function, the caller
 * should request insertion at the head unless the order [order, oind) queues
 * are known to be empty.  The objective being to reduce the likelihood of
 * long-term fragmentation by promoting contemporaneous allocation and
 * (hopefully) deallocation.
 */
static __inline void
vm_phys_split_pages(vm_page_t m, int oind, struct vm_freelist *fl, int order,
    int tail)
{
	vm_page_t m_buddy;

	while (oind > order) {
		oind--;
		m_buddy = &m[1 << oind];
		KASSERT(m_buddy->order == VM_NFREEORDER,
		    ("vm_phys_split_pages: page %p has unexpected order %d",
		    m_buddy, m_buddy->order));
		vm_freelist_add(fl, m_buddy, oind, tail);
        }
}

/*
 * Add the physical pages [m, m + npages) at the end of a power-of-two aligned
 * and sized set to the specified free list.
 *
 * When this function is called by a page allocation function, the caller
 * should request insertion at the head unless the lower-order queues are
 * known to be empty.  The objective being to reduce the likelihood of long-
 * term fragmentation by promoting contemporaneous allocation and (hopefully)
 * deallocation.
 *
 * The physical page m's buddy must not be free.
 */
static void
vm_phys_enq_range(vm_page_t m, u_int npages, struct vm_freelist *fl, int tail)
{
	u_int n;
	int order;

	KASSERT(npages > 0, ("vm_phys_enq_range: npages is 0"));
	KASSERT(((VM_PAGE_TO_PHYS(m) + npages * PAGE_SIZE) &
	    ((PAGE_SIZE << (fls(npages) - 1)) - 1)) == 0,
	    ("vm_phys_enq_range: page %p and npages %u are misaligned",
	    m, npages));
	do {
		KASSERT(m->order == VM_NFREEORDER,
		    ("vm_phys_enq_range: page %p has unexpected order %d",
		    m, m->order));
		order = ffs(npages) - 1;
		KASSERT(order < VM_NFREEORDER,
		    ("vm_phys_enq_range: order %d is out of range", order));
		vm_freelist_add(fl, m, order, tail);
		n = 1 << order;
		m += n;
		npages -= n;
	} while (npages > 0);
}

/*
 * Set the pool for a contiguous, power of two-sized set of physical pages. 
 */
static void
vm_phys_set_pool(int pool, vm_page_t m, int order)
{
	vm_page_t m_tmp;

	for (m_tmp = m; m_tmp < &m[1 << order]; m_tmp++)
		m_tmp->pool = pool;
}

/*
 * Tries to allocate the specified number of pages from the specified pool
 * within the specified domain.  Returns the actual number of allocated pages
 * and a pointer to each page through the array ma[].
 *
 * The returned pages may not be physically contiguous.  However, in contrast
 * to performing multiple, back-to-back calls to vm_phys_alloc_pages(..., 0),
 * calling this function once to allocate the desired number of pages will
 * avoid wasted time in vm_phys_split_pages().
 *
 * The free page queues for the specified domain must be locked.
 */
int
vm_phys_alloc_npages(int domain, int pool, int npages, vm_page_t ma[])
{
	struct vm_freelist *alt, *fl;
	vm_page_t m;
	int avail, end, flind, freelist, i, need, oind, pind;

	KASSERT(domain >= 0 && domain < vm_ndomains,
	    ("vm_phys_alloc_npages: domain %d is out of range", domain));
	KASSERT(pool < VM_NFREEPOOL,
	    ("vm_phys_alloc_npages: pool %d is out of range", pool));
	KASSERT(npages <= 1 << (VM_NFREEORDER - 1),
	    ("vm_phys_alloc_npages: npages %d is out of range", npages));
	vm_domain_free_assert_locked(VM_DOMAIN(domain));
	i = 0;
	for (freelist = 0; freelist < VM_NFREELIST; freelist++) {
		flind = vm_freelist_to_flind[freelist];
		if (flind < 0)
			continue;
		fl = vm_phys_free_queues[domain][flind][pool];
		for (oind = 0; oind < VM_NFREEORDER; oind++) {
			while ((m = TAILQ_FIRST(&fl[oind].pl)) != NULL) {
				vm_freelist_rem(fl, m, oind);
				avail = 1 << oind;
				need = imin(npages - i, avail);
				for (end = i + need; i < end;)
					ma[i++] = m++;
				if (need < avail) {
					/*
					 * Return excess pages to fl.  Its
					 * order [0, oind) queues are empty.
					 */
					vm_phys_enq_range(m, avail - need, fl,
					    1);
					return (npages);
				} else if (i == npages)
					return (npages);
			}
		}
		for (oind = VM_NFREEORDER - 1; oind >= 0; oind--) {
			for (pind = 0; pind < VM_NFREEPOOL; pind++) {
				alt = vm_phys_free_queues[domain][flind][pind];
				while ((m = TAILQ_FIRST(&alt[oind].pl)) !=
				    NULL) {
					vm_freelist_rem(alt, m, oind);
					vm_phys_set_pool(pool, m, oind);
					avail = 1 << oind;
					need = imin(npages - i, avail);
					for (end = i + need; i < end;)
						ma[i++] = m++;
					if (need < avail) {
						/*
						 * Return excess pages to fl.
						 * Its order [0, oind) queues
						 * are empty.
						 */
						vm_phys_enq_range(m, avail -
						    need, fl, 1);
						return (npages);
					} else if (i == npages)
						return (npages);
				}
			}
		}
	}
	return (i);
}

/*
 * Allocate a contiguous, power of two-sized set of physical pages
 * from the free lists.
 *
 * The free page queues must be locked.
 */
vm_page_t
vm_phys_alloc_pages(int domain, int pool, int order)
{
	vm_page_t m;
	int freelist;

	for (freelist = 0; freelist < VM_NFREELIST; freelist++) {
		m = vm_phys_alloc_freelist_pages(domain, freelist, pool, order);
		if (m != NULL)
			return (m);
	}
	return (NULL);
}

/*
 * Allocate a contiguous, power of two-sized set of physical pages from the
 * specified free list.  The free list must be specified using one of the
 * manifest constants VM_FREELIST_*.
 *
 * The free page queues must be locked.
 */
vm_page_t
vm_phys_alloc_freelist_pages(int domain, int freelist, int pool, int order)
{
	struct vm_freelist *alt, *fl;
	vm_page_t m;
	int oind, pind, flind;

	KASSERT(domain >= 0 && domain < vm_ndomains,
	    ("vm_phys_alloc_freelist_pages: domain %d is out of range",
	    domain));
	KASSERT(freelist < VM_NFREELIST,
	    ("vm_phys_alloc_freelist_pages: freelist %d is out of range",
	    freelist));
	KASSERT(pool < VM_NFREEPOOL,
	    ("vm_phys_alloc_freelist_pages: pool %d is out of range", pool));
	KASSERT(order < VM_NFREEORDER,
	    ("vm_phys_alloc_freelist_pages: order %d is out of range", order));

	flind = vm_freelist_to_flind[freelist];
	/* Check if freelist is present */
	if (flind < 0)
		return (NULL);

	vm_domain_free_assert_locked(VM_DOMAIN(domain));
	fl = &vm_phys_free_queues[domain][flind][pool][0];
	for (oind = order; oind < VM_NFREEORDER; oind++) {
		m = TAILQ_FIRST(&fl[oind].pl);
		if (m != NULL) {
			vm_freelist_rem(fl, m, oind);
			/* The order [order, oind) queues are empty. */
			vm_phys_split_pages(m, oind, fl, order, 1);
			return (m);
		}
	}

	/*
	 * The given pool was empty.  Find the largest
	 * contiguous, power-of-two-sized set of pages in any
	 * pool.  Transfer these pages to the given pool, and
	 * use them to satisfy the allocation.
	 */
	for (oind = VM_NFREEORDER - 1; oind >= order; oind--) {
		for (pind = 0; pind < VM_NFREEPOOL; pind++) {
			alt = &vm_phys_free_queues[domain][flind][pind][0];
			m = TAILQ_FIRST(&alt[oind].pl);
			if (m != NULL) {
				vm_freelist_rem(alt, m, oind);
				vm_phys_set_pool(pool, m, oind);
				/* The order [order, oind) queues are empty. */
				vm_phys_split_pages(m, oind, fl, order, 1);
				return (m);
			}
		}
	}
	return (NULL);
}

/*
 * Find the vm_page corresponding to the given physical address.
 */
vm_page_t
vm_phys_paddr_to_vm_page(vm_paddr_t pa)
{
	struct vm_phys_seg *seg;
	int segind;

	for (segind = 0; segind < vm_phys_nsegs; segind++) {
		seg = &vm_phys_segs[segind];
		if (pa >= seg->start && pa < seg->end)
			return (&seg->first_page[atop(pa - seg->start)]);
	}
	return (NULL);
}

vm_page_t
vm_phys_fictitious_to_vm_page(vm_paddr_t pa)
{
	struct vm_phys_fictitious_seg tmp, *seg;
	vm_page_t m;

	m = NULL;
	tmp.start = pa;
	tmp.end = 0;

	rw_rlock(&vm_phys_fictitious_reg_lock);
	seg = RB_FIND(fict_tree, &vm_phys_fictitious_tree, &tmp);
	rw_runlock(&vm_phys_fictitious_reg_lock);
	if (seg == NULL)
		return (NULL);

	m = &seg->first_page[atop(pa - seg->start)];
	KASSERT((m->flags & PG_FICTITIOUS) != 0, ("%p not fictitious", m));

	return (m);
}

static inline void
vm_phys_fictitious_init_range(vm_page_t range, vm_paddr_t start,
    long page_count, vm_memattr_t memattr)
{
	long i;

	bzero(range, page_count * sizeof(*range));
	for (i = 0; i < page_count; i++) {
		vm_page_initfake(&range[i], start + PAGE_SIZE * i, memattr);
		range[i].oflags &= ~VPO_UNMANAGED;
		range[i].busy_lock = VPB_UNBUSIED;
	}
}

int
vm_phys_fictitious_reg_range(vm_paddr_t start, vm_paddr_t end,
    vm_memattr_t memattr)
{
	struct vm_phys_fictitious_seg *seg;
	vm_page_t fp;
	long page_count;
#ifdef VM_PHYSSEG_DENSE
	long pi, pe;
	long dpage_count;
#endif

	KASSERT(start < end,
	    ("Start of segment isn't less than end (start: %jx end: %jx)",
	    (uintmax_t)start, (uintmax_t)end));

	page_count = (end - start) / PAGE_SIZE;

#ifdef VM_PHYSSEG_DENSE
	pi = atop(start);
	pe = atop(end);
	if (pi >= first_page && (pi - first_page) < vm_page_array_size) {
		fp = &vm_page_array[pi - first_page];
		if ((pe - first_page) > vm_page_array_size) {
			/*
			 * We have a segment that starts inside
			 * of vm_page_array, but ends outside of it.
			 *
			 * Use vm_page_array pages for those that are
			 * inside of the vm_page_array range, and
			 * allocate the remaining ones.
			 */
			dpage_count = vm_page_array_size - (pi - first_page);
			vm_phys_fictitious_init_range(fp, start, dpage_count,
			    memattr);
			page_count -= dpage_count;
			start += ptoa(dpage_count);
			goto alloc;
		}
		/*
		 * We can allocate the full range from vm_page_array,
		 * so there's no need to register the range in the tree.
		 */
		vm_phys_fictitious_init_range(fp, start, page_count, memattr);
		return (0);
	} else if (pe > first_page && (pe - first_page) < vm_page_array_size) {
		/*
		 * We have a segment that ends inside of vm_page_array,
		 * but starts outside of it.
		 */
		fp = &vm_page_array[0];
		dpage_count = pe - first_page;
		vm_phys_fictitious_init_range(fp, ptoa(first_page), dpage_count,
		    memattr);
		end -= ptoa(dpage_count);
		page_count -= dpage_count;
		goto alloc;
	} else if (pi < first_page && pe > (first_page + vm_page_array_size)) {
		/*
		 * Trying to register a fictitious range that expands before
		 * and after vm_page_array.
		 */
		return (EINVAL);
	} else {
alloc:
#endif
		fp = malloc(page_count * sizeof(struct vm_page), M_FICT_PAGES,
		    M_WAITOK);
#ifdef VM_PHYSSEG_DENSE
	}
#endif
	vm_phys_fictitious_init_range(fp, start, page_count, memattr);

	seg = malloc(sizeof(*seg), M_FICT_PAGES, M_WAITOK | M_ZERO);
	seg->start = start;
	seg->end = end;
	seg->first_page = fp;

	rw_wlock(&vm_phys_fictitious_reg_lock);
	RB_INSERT(fict_tree, &vm_phys_fictitious_tree, seg);
	rw_wunlock(&vm_phys_fictitious_reg_lock);

	return (0);
}

void
vm_phys_fictitious_unreg_range(vm_paddr_t start, vm_paddr_t end)
{
	struct vm_phys_fictitious_seg *seg, tmp;
#ifdef VM_PHYSSEG_DENSE
	long pi, pe;
#endif

	KASSERT(start < end,
	    ("Start of segment isn't less than end (start: %jx end: %jx)",
	    (uintmax_t)start, (uintmax_t)end));

#ifdef VM_PHYSSEG_DENSE
	pi = atop(start);
	pe = atop(end);
	if (pi >= first_page && (pi - first_page) < vm_page_array_size) {
		if ((pe - first_page) <= vm_page_array_size) {
			/*
			 * This segment was allocated using vm_page_array
			 * only, there's nothing to do since those pages
			 * were never added to the tree.
			 */
			return;
		}
		/*
		 * We have a segment that starts inside
		 * of vm_page_array, but ends outside of it.
		 *
		 * Calculate how many pages were added to the
		 * tree and free them.
		 */
		start = ptoa(first_page + vm_page_array_size);
	} else if (pe > first_page && (pe - first_page) < vm_page_array_size) {
		/*
		 * We have a segment that ends inside of vm_page_array,
		 * but starts outside of it.
		 */
		end = ptoa(first_page);
	} else if (pi < first_page && pe > (first_page + vm_page_array_size)) {
		/* Since it's not possible to register such a range, panic. */
		panic(
		    "Unregistering not registered fictitious range [%#jx:%#jx]",
		    (uintmax_t)start, (uintmax_t)end);
	}
#endif
	tmp.start = start;
	tmp.end = 0;

	rw_wlock(&vm_phys_fictitious_reg_lock);
	seg = RB_FIND(fict_tree, &vm_phys_fictitious_tree, &tmp);
	if (seg->start != start || seg->end != end) {
		rw_wunlock(&vm_phys_fictitious_reg_lock);
		panic(
		    "Unregistering not registered fictitious range [%#jx:%#jx]",
		    (uintmax_t)start, (uintmax_t)end);
	}
	RB_REMOVE(fict_tree, &vm_phys_fictitious_tree, seg);
	rw_wunlock(&vm_phys_fictitious_reg_lock);
	free(seg->first_page, M_FICT_PAGES);
	free(seg, M_FICT_PAGES);
}

/*
 * Free a contiguous, power of two-sized set of physical pages.
 *
 * The free page queues must be locked.
 */
void
vm_phys_free_pages(vm_page_t m, int order)
{
	struct vm_freelist *fl;
	struct vm_phys_seg *seg;
	vm_paddr_t pa;
	vm_page_t m_buddy;

	KASSERT(m->order == VM_NFREEORDER,
	    ("vm_phys_free_pages: page %p has unexpected order %d",
	    m, m->order));
	KASSERT(m->pool < VM_NFREEPOOL,
	    ("vm_phys_free_pages: page %p has unexpected pool %d",
	    m, m->pool));
	KASSERT(order < VM_NFREEORDER,
	    ("vm_phys_free_pages: order %d is out of range", order));
	seg = &vm_phys_segs[m->segind];
	vm_domain_free_assert_locked(VM_DOMAIN(seg->domain));
	if (order < VM_NFREEORDER - 1) {
		pa = VM_PAGE_TO_PHYS(m);
		do {
			pa ^= ((vm_paddr_t)1 << (PAGE_SHIFT + order));
			if (pa < seg->start || pa >= seg->end)
				break;
			m_buddy = &seg->first_page[atop(pa - seg->start)];
			if (m_buddy->order != order)
				break;
			fl = (*seg->free_queues)[m_buddy->pool];
			vm_freelist_rem(fl, m_buddy, order);
			if (m_buddy->pool != m->pool)
				vm_phys_set_pool(m->pool, m_buddy, order);
			order++;
			pa &= ~(((vm_paddr_t)1 << (PAGE_SHIFT + order)) - 1);
			m = &seg->first_page[atop(pa - seg->start)];
		} while (order < VM_NFREEORDER - 1);
	}
	fl = (*seg->free_queues)[m->pool];
	vm_freelist_add(fl, m, order, 1);
}

/*
 * Return the largest possible order of a set of pages starting at m.
 */
static int
max_order(vm_page_t m)
{

	/*
	 * Unsigned "min" is used here so that "order" is assigned
	 * "VM_NFREEORDER - 1" when "m"'s physical address is zero
	 * or the low-order bits of its physical address are zero
	 * because the size of a physical address exceeds the size of
	 * a long.
	 */
	return (min(ffsl(VM_PAGE_TO_PHYS(m) >> PAGE_SHIFT) - 1,
	    VM_NFREEORDER - 1));
}

/*
 * Free a contiguous, arbitrarily sized set of physical pages, without
 * merging across set boundaries.
 *
 * The free page queues must be locked.
 */
void
vm_phys_enqueue_contig(vm_page_t m, u_long npages)
{
	struct vm_freelist *fl;
	struct vm_phys_seg *seg;
	vm_page_t m_end;
	int order;

	/*
	 * Avoid unnecessary coalescing by freeing the pages in the largest
	 * possible power-of-two-sized subsets.
	 */
	vm_domain_free_assert_locked(vm_pagequeue_domain(m));
	seg = &vm_phys_segs[m->segind];
	fl = (*seg->free_queues)[m->pool];
	m_end = m + npages;
	/* Free blocks of increasing size. */
	while ((order = max_order(m)) < VM_NFREEORDER - 1 &&
	    m + (1 << order) <= m_end) {
		KASSERT(seg == &vm_phys_segs[m->segind],
		    ("%s: page range [%p,%p) spans multiple segments",
		    __func__, m_end - npages, m));
		vm_freelist_add(fl, m, order, 1);
		m += 1 << order;
	}
	/* Free blocks of maximum size. */
	while (m + (1 << order) <= m_end) {
		KASSERT(seg == &vm_phys_segs[m->segind],
		    ("%s: page range [%p,%p) spans multiple segments",
		    __func__, m_end - npages, m));
		vm_freelist_add(fl, m, order, 1);
		m += 1 << order;
	}
	/* Free blocks of diminishing size. */
	while (m < m_end) {
		KASSERT(seg == &vm_phys_segs[m->segind],
		    ("%s: page range [%p,%p) spans multiple segments",
		    __func__, m_end - npages, m));
		order = flsl(m_end - m) - 1;
		vm_freelist_add(fl, m, order, 1);
		m += 1 << order;
	}
}

/*
 * Free a contiguous, arbitrarily sized set of physical pages.
 *
 * The free page queues must be locked.
 */
void
vm_phys_free_contig(vm_page_t m, u_long npages)
{
	int order_start, order_end;
	vm_page_t m_start, m_end;

	vm_domain_free_assert_locked(vm_pagequeue_domain(m));

	m_start = m;
	order_start = max_order(m_start);
	if (order_start < VM_NFREEORDER - 1)
		m_start += 1 << order_start;
	m_end = m + npages;
	order_end = max_order(m_end);
	if (order_end < VM_NFREEORDER - 1)
		m_end -= 1 << order_end;
	/*
	 * Avoid unnecessary coalescing by freeing the pages at the start and
	 * end of the range last.
	 */
	if (m_start < m_end)
		vm_phys_enqueue_contig(m_start, m_end - m_start);
	if (order_start < VM_NFREEORDER - 1)
		vm_phys_free_pages(m, order_start);
	if (order_end < VM_NFREEORDER - 1)
		vm_phys_free_pages(m_end, order_end);
}

/*
 * Scan physical memory between the specified addresses "low" and "high" for a
 * run of contiguous physical pages that satisfy the specified conditions, and
 * return the lowest page in the run.  The specified "alignment" determines
 * the alignment of the lowest physical page in the run.  If the specified
 * "boundary" is non-zero, then the run of physical pages cannot span a
 * physical address that is a multiple of "boundary".
 *
 * "npages" must be greater than zero.  Both "alignment" and "boundary" must
 * be a power of two.
 */
vm_page_t
vm_phys_scan_contig(int domain, u_long npages, vm_paddr_t low, vm_paddr_t high,
    u_long alignment, vm_paddr_t boundary, int options)
{
	vm_paddr_t pa_end;
	vm_page_t m_end, m_run, m_start;
	struct vm_phys_seg *seg;
	int segind;

	KASSERT(npages > 0, ("npages is 0"));
	KASSERT(powerof2(alignment), ("alignment is not a power of 2"));
	KASSERT(powerof2(boundary), ("boundary is not a power of 2"));
	if (low >= high)
		return (NULL);
	for (segind = 0; segind < vm_phys_nsegs; segind++) {
		seg = &vm_phys_segs[segind];
		if (seg->domain != domain)
			continue;
		if (seg->start >= high)
			break;
		if (low >= seg->end)
			continue;
		if (low <= seg->start)
			m_start = seg->first_page;
		else
			m_start = &seg->first_page[atop(low - seg->start)];
		if (high < seg->end)
			pa_end = high;
		else
			pa_end = seg->end;
		if (pa_end - VM_PAGE_TO_PHYS(m_start) < ptoa(npages))
			continue;
		m_end = &seg->first_page[atop(pa_end - seg->start)];
		m_run = vm_page_scan_contig(npages, m_start, m_end,
		    alignment, boundary, options);
		if (m_run != NULL)
			return (m_run);
	}
	return (NULL);
}

/*
 * Search for the given physical page "m" in the free lists.  If the search
 * succeeds, remove "m" from the free lists and return TRUE.  Otherwise, return
 * FALSE, indicating that "m" is not in the free lists.
 *
 * The free page queues must be locked.
 */
boolean_t
vm_phys_unfree_page(vm_page_t m)
{
	struct vm_freelist *fl;
	struct vm_phys_seg *seg;
	vm_paddr_t pa, pa_half;
	vm_page_t m_set, m_tmp;
	int order;

	/*
	 * First, find the contiguous, power of two-sized set of free
	 * physical pages containing the given physical page "m" and
	 * assign it to "m_set".
	 */
	seg = &vm_phys_segs[m->segind];
	vm_domain_free_assert_locked(VM_DOMAIN(seg->domain));
	for (m_set = m, order = 0; m_set->order == VM_NFREEORDER &&
	    order < VM_NFREEORDER - 1; ) {
		order++;
		pa = m->phys_addr & (~(vm_paddr_t)0 << (PAGE_SHIFT + order));
		if (pa >= seg->start)
			m_set = &seg->first_page[atop(pa - seg->start)];
		else
			return (FALSE);
	}
	if (m_set->order < order)
		return (FALSE);
	if (m_set->order == VM_NFREEORDER)
		return (FALSE);
	KASSERT(m_set->order < VM_NFREEORDER,
	    ("vm_phys_unfree_page: page %p has unexpected order %d",
	    m_set, m_set->order));

	/*
	 * Next, remove "m_set" from the free lists.  Finally, extract
	 * "m" from "m_set" using an iterative algorithm: While "m_set"
	 * is larger than a page, shrink "m_set" by returning the half
	 * of "m_set" that does not contain "m" to the free lists.
	 */
	fl = (*seg->free_queues)[m_set->pool];
	order = m_set->order;
	vm_freelist_rem(fl, m_set, order);
	while (order > 0) {
		order--;
		pa_half = m_set->phys_addr ^ (1 << (PAGE_SHIFT + order));
		if (m->phys_addr < pa_half)
			m_tmp = &seg->first_page[atop(pa_half - seg->start)];
		else {
			m_tmp = m_set;
			m_set = &seg->first_page[atop(pa_half - seg->start)];
		}
		vm_freelist_add(fl, m_tmp, order, 0);
	}
	KASSERT(m_set == m, ("vm_phys_unfree_page: fatal inconsistency"));
	return (TRUE);
}

/*
 * Find a run of contiguous physical pages from the specified page list.
 */
static vm_page_t
vm_phys_find_freelist_contig(struct vm_freelist *fl, int oind, u_long npages,
    vm_paddr_t low, vm_paddr_t high, u_long alignment, vm_paddr_t boundary)
{
	struct vm_phys_seg *seg;
	vm_paddr_t frag, lbound, pa, page_size, pa_end, pa_pre, size;
	vm_page_t m, m_listed, m_ret;
	int order;

	KASSERT(npages > 0, ("npages is 0"));
	KASSERT(powerof2(alignment), ("alignment is not a power of 2"));
	KASSERT(powerof2(boundary), ("boundary is not a power of 2"));
	/* Search for a run satisfying the specified conditions. */
	page_size = PAGE_SIZE;
	size = npages << PAGE_SHIFT;
	frag = (npages & ~(~0UL << oind)) << PAGE_SHIFT;
	TAILQ_FOREACH(m_listed, &fl[oind].pl, listq) {
		/*
		 * Determine if the address range starting at pa is
		 * too low.
		 */
		pa = VM_PAGE_TO_PHYS(m_listed);
		if (pa < low)
			continue;

		/*
		 * If this is not the first free oind-block in this range, bail
		 * out. We have seen the first free block already, or will see
		 * it before failing to find an appropriate range.
		 */
		seg = &vm_phys_segs[m_listed->segind];
		lbound = low > seg->start ? low : seg->start;
		pa_pre = pa - (page_size << oind);
		m = &seg->first_page[atop(pa_pre - seg->start)];
		if (pa != 0 && pa_pre >= lbound && m->order == oind)
			continue;

		if (!vm_addr_align_ok(pa, alignment))
			/* Advance to satisfy alignment condition. */
			pa = roundup2(pa, alignment);
		else if (frag != 0 && lbound + frag <= pa) {
			/*
			 * Back up to the first aligned free block in this
			 * range, without moving below lbound.
			 */
			pa_end = pa;
			for (order = oind - 1; order >= 0; order--) {
				pa_pre = pa_end - (page_size << order);
				if (!vm_addr_align_ok(pa_pre, alignment))
					break;
				m = &seg->first_page[atop(pa_pre - seg->start)];
				if (pa_pre >= lbound && m->order == order)
					pa_end = pa_pre;
			}
			/*
			 * If the extra small blocks are enough to complete the
			 * fragment, use them.  Otherwise, look to allocate the
			 * fragment at the other end.
			 */
			if (pa_end + frag <= pa)
				pa = pa_end;
		}

		/* Advance as necessary to satisfy boundary conditions. */
		if (!vm_addr_bound_ok(pa, size, boundary))
			pa = roundup2(pa + 1, boundary);
		pa_end = pa + size;

		/*
		 * Determine if the address range is valid (without overflow in
		 * pa_end calculation), and fits within the segment.
		 */
		if (pa_end < pa || seg->end < pa_end)
			continue;

		m_ret = &seg->first_page[atop(pa - seg->start)];

		/*
		 * Determine whether there are enough free oind-blocks here to
		 * satisfy the allocation request.
		 */
		pa = VM_PAGE_TO_PHYS(m_listed);
		do {
			pa += page_size << oind;
			if (pa >= pa_end)
				return (m_ret);
			m = &seg->first_page[atop(pa - seg->start)];
		} while (oind == m->order);

		/*
		 * Determine if an additional series of free blocks of
		 * diminishing size can help to satisfy the allocation request.
		 */
		while (m->order < oind &&
		    pa + 2 * (page_size << m->order) > pa_end) {
			pa += page_size << m->order;
			if (pa >= pa_end)
				return (m_ret);
			m = &seg->first_page[atop(pa - seg->start)];
		}
	}
	return (NULL);
}

/*
 * Find a run of contiguous physical pages from the specified free list
 * table.
 */
static vm_page_t
vm_phys_find_queues_contig(
    struct vm_freelist (*queues)[VM_NFREEPOOL][VM_NFREEORDER_MAX],
    u_long npages, vm_paddr_t low, vm_paddr_t high,
    u_long alignment, vm_paddr_t boundary)
{
	struct vm_freelist *fl;
	vm_page_t m_ret;
	vm_paddr_t pa, pa_end, size;
	int oind, order, pind;

	KASSERT(npages > 0, ("npages is 0"));
	KASSERT(powerof2(alignment), ("alignment is not a power of 2"));
	KASSERT(powerof2(boundary), ("boundary is not a power of 2"));
	/* Compute the queue that is the best fit for npages. */
	order = flsl(npages - 1);
	/* Search for a large enough free block. */
	size = npages << PAGE_SHIFT;
	for (oind = order; oind < VM_NFREEORDER; oind++) {
		for (pind = 0; pind < VM_NFREEPOOL; pind++) {
			fl = (*queues)[pind];
			TAILQ_FOREACH(m_ret, &fl[oind].pl, listq) {
				/*
				 * Determine if the address range starting at pa
				 * is within the given range, satisfies the
				 * given alignment, and does not cross the given
				 * boundary.
				 */
				pa = VM_PAGE_TO_PHYS(m_ret);
				pa_end = pa + size;
				if (low <= pa && pa_end <= high &&
				    vm_addr_ok(pa, size, alignment, boundary))
					return (m_ret);
			}
		}
	}
	if (order < VM_NFREEORDER)
		return (NULL);
	/* Search for a long-enough sequence of small blocks. */
	oind = VM_NFREEORDER - 1;
	for (pind = 0; pind < VM_NFREEPOOL; pind++) {
		fl = (*queues)[pind];
		m_ret = vm_phys_find_freelist_contig(fl, oind, npages,
		    low, high, alignment, boundary);
		if (m_ret != NULL)
			return (m_ret);
	}
	return (NULL);
}

/*
 * Allocate a contiguous set of physical pages of the given size
 * "npages" from the free lists.  All of the physical pages must be at
 * or above the given physical address "low" and below the given
 * physical address "high".  The given value "alignment" determines the
 * alignment of the first physical page in the set.  If the given value
 * "boundary" is non-zero, then the set of physical pages cannot cross
 * any physical address boundary that is a multiple of that value.  Both
 * "alignment" and "boundary" must be a power of two.
 */
vm_page_t
vm_phys_alloc_contig(int domain, u_long npages, vm_paddr_t low, vm_paddr_t high,
    u_long alignment, vm_paddr_t boundary)
{
	vm_paddr_t pa_end, pa_start;
	struct vm_freelist *fl;
	vm_page_t m, m_run;
	struct vm_phys_seg *seg;
	struct vm_freelist (*queues)[VM_NFREEPOOL][VM_NFREEORDER_MAX];
	int oind, segind;

	KASSERT(npages > 0, ("npages is 0"));
	KASSERT(powerof2(alignment), ("alignment is not a power of 2"));
	KASSERT(powerof2(boundary), ("boundary is not a power of 2"));
	vm_domain_free_assert_locked(VM_DOMAIN(domain));
	if (low >= high)
		return (NULL);
	queues = NULL;
	m_run = NULL;
	for (segind = vm_phys_nsegs - 1; segind >= 0; segind--) {
		seg = &vm_phys_segs[segind];
		if (seg->start >= high || seg->domain != domain)
			continue;
		if (low >= seg->end)
			break;
		if (low <= seg->start)
			pa_start = seg->start;
		else
			pa_start = low;
		if (high < seg->end)
			pa_end = high;
		else
			pa_end = seg->end;
		if (pa_end - pa_start < ptoa(npages))
			continue;
		/*
		 * If a previous segment led to a search using
		 * the same free lists as would this segment, then
		 * we've actually already searched within this
		 * too.  So skip it.
		 */
		if (seg->free_queues == queues)
			continue;
		queues = seg->free_queues;
		m_run = vm_phys_find_queues_contig(queues, npages,
		    low, high, alignment, boundary);
		if (m_run != NULL)
			break;
	}
	if (m_run == NULL)
		return (NULL);

	/* Allocate pages from the page-range found. */
	for (m = m_run; m < &m_run[npages]; m = &m[1 << oind]) {
		fl = (*queues)[m->pool];
		oind = m->order;
		vm_freelist_rem(fl, m, oind);
		if (m->pool != VM_FREEPOOL_DEFAULT)
			vm_phys_set_pool(VM_FREEPOOL_DEFAULT, m, oind);
	}
	/* Return excess pages to the free lists. */
	if (&m_run[npages] < m) {
		fl = (*queues)[VM_FREEPOOL_DEFAULT];
		vm_phys_enq_range(&m_run[npages], m - &m_run[npages], fl, 0);
	}
	return (m_run);
}

/*
 * Return the index of the first unused slot which may be the terminating
 * entry.
 */
static int
vm_phys_avail_count(void)
{
	int i;

	for (i = 0; phys_avail[i + 1]; i += 2)
		continue;
	if (i > PHYS_AVAIL_ENTRIES)
		panic("Improperly terminated phys_avail %d entries", i);

	return (i);
}

/*
 * Assert that a phys_avail entry is valid.
 */
static void
vm_phys_avail_check(int i)
{
	if (phys_avail[i] & PAGE_MASK)
		panic("Unaligned phys_avail[%d]: %#jx", i,
		    (intmax_t)phys_avail[i]);
	if (phys_avail[i+1] & PAGE_MASK)
		panic("Unaligned phys_avail[%d + 1]: %#jx", i,
		    (intmax_t)phys_avail[i]);
	if (phys_avail[i + 1] < phys_avail[i])
		panic("phys_avail[%d] start %#jx < end %#jx", i,
		    (intmax_t)phys_avail[i], (intmax_t)phys_avail[i+1]);
}

/*
 * Return the index of an overlapping phys_avail entry or -1.
 */
#ifdef NUMA
static int
vm_phys_avail_find(vm_paddr_t pa)
{
	int i;

	for (i = 0; phys_avail[i + 1]; i += 2)
		if (phys_avail[i] <= pa && phys_avail[i + 1] > pa)
			return (i);
	return (-1);
}
#endif

/*
 * Return the index of the largest entry.
 */
int
vm_phys_avail_largest(void)
{
	vm_paddr_t sz, largesz;
	int largest;
	int i;

	largest = 0;
	largesz = 0;
	for (i = 0; phys_avail[i + 1]; i += 2) {
		sz = vm_phys_avail_size(i);
		if (sz > largesz) {
			largesz = sz;
			largest = i;
		}
	}

	return (largest);
}

vm_paddr_t
vm_phys_avail_size(int i)
{

	return (phys_avail[i + 1] - phys_avail[i]);
}

/*
 * Split an entry at the address 'pa'.  Return zero on success or errno.
 */
static int
vm_phys_avail_split(vm_paddr_t pa, int i)
{
	int cnt;

	vm_phys_avail_check(i);
	if (pa <= phys_avail[i] || pa >= phys_avail[i + 1])
		panic("vm_phys_avail_split: invalid address");
	cnt = vm_phys_avail_count();
	if (cnt >= PHYS_AVAIL_ENTRIES)
		return (ENOSPC);
	memmove(&phys_avail[i + 2], &phys_avail[i],
	    (cnt - i) * sizeof(phys_avail[0]));
	phys_avail[i + 1] = pa;
	phys_avail[i + 2] = pa;
	vm_phys_avail_check(i);
	vm_phys_avail_check(i+2);

	return (0);
}

/*
 * Check if a given physical address can be included as part of a crash dump.
 */
bool
vm_phys_is_dumpable(vm_paddr_t pa)
{
	vm_page_t m;
	int i;

	if ((m = vm_phys_paddr_to_vm_page(pa)) != NULL)
		return ((m->flags & PG_NODUMP) == 0);

	for (i = 0; dump_avail[i] != 0 || dump_avail[i + 1] != 0; i += 2) {
		if (pa >= dump_avail[i] && pa < dump_avail[i + 1])
			return (true);
	}
	return (false);
}

void
vm_phys_early_add_seg(vm_paddr_t start, vm_paddr_t end)
{
	struct vm_phys_seg *seg;

	if (vm_phys_early_nsegs == -1)
		panic("%s: called after initialization", __func__);
	if (vm_phys_early_nsegs == nitems(vm_phys_early_segs))
		panic("%s: ran out of early segments", __func__);

	seg = &vm_phys_early_segs[vm_phys_early_nsegs++];
	seg->start = start;
	seg->end = end;
}

/*
 * This routine allocates NUMA node specific memory before the page
 * allocator is bootstrapped.
 */
vm_paddr_t
vm_phys_early_alloc(int domain, size_t alloc_size)
{
#ifdef NUMA
	int mem_index;
#endif
	int i, biggestone;
	vm_paddr_t pa, mem_start, mem_end, size, biggestsize, align;

	KASSERT(domain == -1 || (domain >= 0 && domain < vm_ndomains),
	    ("%s: invalid domain index %d", __func__, domain));

	/*
	 * Search the mem_affinity array for the biggest address
	 * range in the desired domain.  This is used to constrain
	 * the phys_avail selection below.
	 */
	biggestsize = 0;
	mem_start = 0;
	mem_end = -1;
#ifdef NUMA
	mem_index = 0;
	if (mem_affinity != NULL) {
		for (i = 0;; i++) {
			size = mem_affinity[i].end - mem_affinity[i].start;
			if (size == 0)
				break;
			if (domain != -1 && mem_affinity[i].domain != domain)
				continue;
			if (size > biggestsize) {
				mem_index = i;
				biggestsize = size;
			}
		}
		mem_start = mem_affinity[mem_index].start;
		mem_end = mem_affinity[mem_index].end;
	}
#endif

	/*
	 * Now find biggest physical segment in within the desired
	 * numa domain.
	 */
	biggestsize = 0;
	biggestone = 0;
	for (i = 0; phys_avail[i + 1] != 0; i += 2) {
		/* skip regions that are out of range */
		if (phys_avail[i+1] - alloc_size < mem_start ||
		    phys_avail[i+1] > mem_end)
			continue;
		size = vm_phys_avail_size(i);
		if (size > biggestsize) {
			biggestone = i;
			biggestsize = size;
		}
	}
	alloc_size = round_page(alloc_size);

	/*
	 * Grab single pages from the front to reduce fragmentation.
	 */
	if (alloc_size == PAGE_SIZE) {
		pa = phys_avail[biggestone];
		phys_avail[biggestone] += PAGE_SIZE;
		vm_phys_avail_check(biggestone);
		return (pa);
	}

	/*
	 * Naturally align large allocations.
	 */
	align = phys_avail[biggestone + 1] & (alloc_size - 1);
	if (alloc_size + align > biggestsize)
		panic("cannot find a large enough size\n");
	if (align != 0 &&
	    vm_phys_avail_split(phys_avail[biggestone + 1] - align,
	    biggestone) != 0)
		/* Wasting memory. */
		phys_avail[biggestone + 1] -= align;

	phys_avail[biggestone + 1] -= alloc_size;
	vm_phys_avail_check(biggestone);
	pa = phys_avail[biggestone + 1];
	return (pa);
}

void
vm_phys_early_startup(void)
{
	struct vm_phys_seg *seg;
	int i;

	for (i = 0; phys_avail[i + 1] != 0; i += 2) {
		phys_avail[i] = round_page(phys_avail[i]);
		phys_avail[i + 1] = trunc_page(phys_avail[i + 1]);
	}

	for (i = 0; i < vm_phys_early_nsegs; i++) {
		seg = &vm_phys_early_segs[i];
		vm_phys_add_seg(seg->start, seg->end);
	}
	vm_phys_early_nsegs = -1;

#ifdef NUMA
	/* Force phys_avail to be split by domain. */
	if (mem_affinity != NULL) {
		int idx;

		for (i = 0; mem_affinity[i].end != 0; i++) {
			idx = vm_phys_avail_find(mem_affinity[i].start);
			if (idx != -1 &&
			    phys_avail[idx] != mem_affinity[i].start)
				vm_phys_avail_split(mem_affinity[i].start, idx);
			idx = vm_phys_avail_find(mem_affinity[i].end);
			if (idx != -1 &&
			    phys_avail[idx] != mem_affinity[i].end)
				vm_phys_avail_split(mem_affinity[i].end, idx);
		}
	}
#endif
}

#ifdef DDB
/*
 * Show the number of physical pages in each of the free lists.
 */
DB_SHOW_COMMAND_FLAGS(freepages, db_show_freepages, DB_CMD_MEMSAFE)
{
	struct vm_freelist *fl;
	int flind, oind, pind, dom;

	for (dom = 0; dom < vm_ndomains; dom++) {
		db_printf("DOMAIN: %d\n", dom);
		for (flind = 0; flind < vm_nfreelists; flind++) {
			db_printf("FREE LIST %d:\n"
			    "\n  ORDER (SIZE)  |  NUMBER"
			    "\n              ", flind);
			for (pind = 0; pind < VM_NFREEPOOL; pind++)
				db_printf("  |  POOL %d", pind);
			db_printf("\n--            ");
			for (pind = 0; pind < VM_NFREEPOOL; pind++)
				db_printf("-- --      ");
			db_printf("--\n");
			for (oind = VM_NFREEORDER - 1; oind >= 0; oind--) {
				db_printf("  %2.2d (%6.6dK)", oind,
				    1 << (PAGE_SHIFT - 10 + oind));
				for (pind = 0; pind < VM_NFREEPOOL; pind++) {
				fl = vm_phys_free_queues[dom][flind][pind];
					db_printf("  |  %6.6d", fl[oind].lcnt);
				}
				db_printf("\n");
			}
			db_printf("\n");
		}
		db_printf("\n");
	}
}
#endif

#define VM_PHYS_SEARCH_CHUNK_ORDER (12)
#define VM_PHYS_SEARCH_CHUNK_NPAGES (1 << (VM_PHYS_SEARCH_CHUNK_ORDER))
#define VM_PHYS_SEARCH_CHUNK_SIZE (1 << (PAGE_SHIFT + VM_PHYS_SEARCH_CHUNK_ORDER))
#define VM_PHYS_SEARCH_CHUNK_MASK (VM_PHYS_SEARCH_CHUNK_SIZE - 1)
#define VM_PHYS_SEARCH_IDX_TO_PADDR(i) \
        ((i) << ((VM_PHYS_SEARCH_CHUNK_ORDER) + PAGE_SHIFT))
#define VM_PHYS_PADDR_TO_CHUNK_IDX(p)          \
	(((p) & ~VM_PHYS_SEARCH_CHUNK_MASK) >> \
   ((VM_PHYS_SEARCH_CHUNK_ORDER) + PAGE_SHIFT))
#define VM_PHYS_HOLECNT_HI ((1 << (VM_PHYS_SEARCH_CHUNK_ORDER)) - 100)
#define VM_PHYS_HOLECNT_LO (16)


struct vm_phys_subseg {
       struct vm_compact_region region;
        SLIST_ENTRY(vm_phys_subseg) link;
};
SLIST_HEAD(vm_phys_subseg_head, vm_phys_subseg);

struct vm_phys_search_chunk {
	int holecnt;
  int score;
	int skipidx;
	struct vm_phys_subseg_head *shp;
};

struct vm_phys_search_index {
	struct vm_phys_search_chunk *chunks;
	int nchunks;
	vm_paddr_t dom_start;
	vm_paddr_t dom_end;
};
static struct vm_phys_search_index vm_phys_search_index[MAXMEMDOM];

/*
 * Allocates physical memory required for the memory compaction search index.
 */
void
vm_phys_search_index_startup(vm_offset_t *vaddr)
{
	struct vm_phys_search_index *cur_idx;
	vm_paddr_t pa;
	vm_paddr_t dom_start, dom_end;
	size_t alloc_size;
	int dom_nsearch_chunks;
	int i;

	for (int dom = 0; dom < vm_ndomains; dom++) {
		cur_idx = &vm_phys_search_index[dom];
		dom_nsearch_chunks = 0;
		/* Calculate number of of search index chunks for current domain
		 */
    if(mem_affinity != NULL){
            for (i = 0; mem_affinity[i].end != 0; i++) {
                    if (mem_affinity[i].domain == dom) {
                            dom_start = mem_affinity[i].start;
                            while (mem_affinity[i].domain == dom) {
                                    i++;
                            }
                            dom_end = mem_affinity[i - 1].end;
                    }
            }
    } else {
            dom_start = phys_avail[0];
            i = 1;
            while (phys_avail[i + 1] != 0) {
                    i++;
            }
            dom_end = phys_avail[i];
    }
		/* Allocate search index for current domain */
		dom_nsearch_chunks = atop(dom_end - dom_start) /
		    VM_PHYS_SEARCH_CHUNK_NPAGES;
		/* Add additional chunks if beginning and start aren't search
		 * chunk-aligned. */
		if (dom_start & VM_PHYS_SEARCH_CHUNK_MASK)
			dom_nsearch_chunks++;
		if (dom_end & VM_PHYS_SEARCH_CHUNK_MASK)
			dom_nsearch_chunks++;

		alloc_size = round_page(
		    dom_nsearch_chunks * sizeof(struct vm_phys_search_chunk));
		pa = vm_phys_early_alloc(dom, alloc_size);

		/* Map and zero the array */
		cur_idx->chunks = (void *)(uintptr_t)pmap_map(vaddr, pa,
		    pa + alloc_size, VM_PROT_READ | VM_PROT_WRITE);
		cur_idx->nchunks = dom_nsearch_chunks;
		cur_idx->dom_start = dom_start;
		cur_idx->dom_end = dom_end;

		if (cur_idx->chunks == NULL) {
			panic("Unable to allocate search index for domain %d\n",
			    dom);
		}
		bzero(cur_idx->chunks, alloc_size);
	}
}

static void
vm_phys_update_search_index(vm_page_t m, int order, bool alloc)
{

	struct vm_phys_search_index *sip =
	    &vm_phys_search_index[vm_page_domain(m)];
	int dom_start_idx = VM_PHYS_PADDR_TO_CHUNK_IDX(sip->dom_start);
	int search_chunk_idx = VM_PHYS_PADDR_TO_CHUNK_IDX(m->phys_addr) -
	    dom_start_idx;
	int pgcnt = 1 << order;

	KASSERT(search_chunk_idx < sip->nchunks,
	    ("%s: Attempting to access a nonexistent search chunk", __func__));

  /* Update chunk hole count */
	sip->chunks[search_chunk_idx].holecnt += alloc ? -pgcnt : pgcnt;
	KASSERT(sip->chunks[search_chunk_idx].holecnt >= 0 && sip->chunks[search_chunk_idx].holecnt <=
          VM_PHYS_SEARCH_CHUNK_NPAGES,
	    ("%s: inconsistent hole count: %d",
       __func__, sip->chunks[search_chunk_idx].holecnt));

  /* Update chunk fragmentation score */
  if(order == 0){
          sip->chunks[search_chunk_idx].score += alloc ? -1 : 1;
          if(sip->chunks[search_chunk_idx].score < 0)
                  sip->chunks[search_chunk_idx].score = 0;
  }
}

static void
vm_phys_chunk_register_hole(struct vm_phys_search_chunk *cp,
    vm_paddr_t hole_start, vm_paddr_t hole_end)
{
	struct vm_phys_subseg *ssp;

	if (cp->shp == NULL) {
		vm_paddr_t chunk_start = hole_start &
		    ~VM_PHYS_SEARCH_CHUNK_MASK;
		cp->shp = malloc(sizeof(*cp->shp), M_TEMP, M_ZERO | M_WAITOK);
		SLIST_INIT(cp->shp);
		/* Split chunk into a subseg */
		ssp = malloc(sizeof(*ssp), M_TEMP, M_ZERO | M_WAITOK);
		ssp->region.start = chunk_start;
		ssp->region.end = chunk_start + VM_PHYS_SEARCH_CHUNK_SIZE;

		SLIST_INSERT_HEAD(cp->shp, ssp, link);
	}

	/*
	 * Holes are ordered by paddr - hole registration will
	 * thus always affect the last subsegment in the list.
	 * Take last subseg and split it.
	 */
	ssp = SLIST_FIRST(cp->shp);
	while (SLIST_NEXT(ssp, link)) {
		ssp = SLIST_NEXT(ssp, link);
	}

	if (hole_start == ssp->region.start) {
		ssp->region.start = hole_end;
	} else if (hole_end == ssp->region.end) {
		ssp->region.end = hole_start;
	} else { /* Hole splits the subseg - create and enqueue new subseg */
	  struct vm_phys_subseg *nssp = malloc(sizeof(*nssp), M_TEMP,
		    M_ZERO | M_WAITOK);
		nssp->region.start = hole_end;
		nssp->region.end = ssp->region.end;
		ssp->region.end = hole_start;
		SLIST_INSERT_AFTER(ssp, nssp, link);
	}
}

/*
 * Populates compaction search index with hole information.
 */
static void
vm_phys_compact_init_holes(void){
        int dom;
	struct vm_phys_search_index *sip;
	struct vm_phys_search_chunk *start_chunk, *end_chunk;
	struct vm_phys_hole *hp;
	int start_idx, end_idx;

	for (dom = 0; dom < vm_ndomains; dom++) {
		sip = &vm_phys_search_index[dom];

		/* Add hole information to domain search chunks */
		for (int i = 0; i < vm_phys_nholes; i++) {
			hp = &vm_phys_holes[i];
			if (hp->domain != dom)
				continue;

			start_idx = VM_PHYS_PADDR_TO_CHUNK_IDX(hp->start -
			    (sip->dom_start & ~VM_PHYS_SEARCH_CHUNK_MASK));
			end_idx = VM_PHYS_PADDR_TO_CHUNK_IDX(hp->end -
			    (sip->dom_start & ~VM_PHYS_SEARCH_CHUNK_MASK));
			start_chunk = &sip->chunks[start_idx];
			end_chunk = &sip->chunks[end_idx];

			/* Hole is completely inside this chunk */
			if (start_chunk == end_chunk) {
				/* Register hole in current chunk. */
				vm_phys_chunk_register_hole(start_chunk,
				    hp->start, hp->end);
			} else { /* Hole spans multiple chunks */
				if (hp->start & VM_PHYS_SEARCH_CHUNK_MASK) {
					/* Partial overlap - register hole in
					 * first chunk. */
					vm_phys_chunk_register_hole(start_chunk,
					    hp->start,
					    (hp->start &
						~VM_PHYS_SEARCH_CHUNK_MASK) +
						VM_PHYS_SEARCH_CHUNK_SIZE);
					start_chunk++;
				}
				/* Mark all chunks that are completely covered
				 * by this hole as invalid. */
				while (start_chunk < end_chunk) {
					start_chunk->skipidx = end_idx;
					start_chunk++;
				}

				if (hp->end & VM_PHYS_SEARCH_CHUNK_MASK) {
					/* Partial overlap - register hole in
					 * last chunk. */
					vm_phys_chunk_register_hole(end_chunk,
					    (hp->end &
						~VM_PHYS_SEARCH_CHUNK_MASK),
					    hp->end);
				}
			}
		}
	}
}


/* Initializes holes and starts compaction kthread. */
static void
vm_phys_init_compact(void *arg)
{
        vm_phys_compact_init_holes();
}

SYSINIT(vm_phys_compact, SI_SUB_KMEM + 1, SI_ORDER_ANY,
    vm_phys_init_compact, NULL);

#define VM_PHYS_COMPACT_SEARCH_REGIONS 5
struct vm_phys_compact_ctx {
	int last_idx;
	struct vm_compact_region region[VM_PHYS_COMPACT_SEARCH_REGIONS];
};

static void
vm_phys_compact_ctx_init(void **p_data)
{
	*p_data = (void *)malloc(sizeof(struct vm_phys_compact_ctx),
	    M_VMCOMPACT, M_ZERO | M_WAITOK);
}

static int
vm_phys_compact_search(struct vm_compact_region_head *headp, int domain, void *p_data)
{
	struct vm_phys_search_chunk *scp;
	struct vm_phys_compact_ctx *ctx = (struct vm_phys_compact_ctx *)p_data;
	struct vm_phys_search_index *sip = &vm_phys_search_index[domain];
  struct vm_phys_subseg *ssegp;
	int idx, region_cnt = 0;
  int ctx_region_cnt = 0;
  int chunks_scanned = 0;

  idx = ctx->last_idx;
  while(chunks_scanned < sip->nchunks && region_cnt < VM_PHYS_COMPACT_SEARCH_REGIONS) {
          for(; chunks_scanned < sip->nchunks && idx < sip->nchunks-1 && region_cnt < VM_PHYS_COMPACT_SEARCH_REGIONS; chunks_scanned++,  idx++) {
                  scp = &sip->chunks[idx];

                  if (scp->skipidx) {
                          idx = scp->skipidx-1;
                          chunks_scanned += (scp->skipidx -1) - idx;
                          continue;
                  }

                  if (scp->score > 1 && scp->holecnt >= VM_PHYS_HOLECNT_LO &&
                      scp->holecnt <= VM_PHYS_HOLECNT_HI) {
                          if (scp->shp) {
                                  /* Enqueue subsegments in chunks with holes. */
                                  SLIST_FOREACH(ssegp, scp->shp, link){
                                          SLIST_INSERT_HEAD(headp, &ssegp->region, entries);
                                          region_cnt++;
                                  }
                          } else {
                                  vm_paddr_t start = VM_PHYS_SEARCH_IDX_TO_PADDR(idx);
                                  vm_paddr_t end = VM_PHYS_SEARCH_IDX_TO_PADDR(idx + 1);

                                          region_cnt++;
                                          ctx->region[ctx_region_cnt].start = start;
                                          ctx->region[ctx_region_cnt].end = end;
                                          SLIST_INSERT_HEAD(headp, &ctx->region[ctx_region_cnt], entries);
                                          ctx_region_cnt++;
                          }
                  }
          }

          idx = (idx + 1) % (sip->nchunks - 1);
  }
  ctx->last_idx = (idx + 1) % (sip->nchunks - 1);



	return SLIST_EMPTY(headp);
}
/*
 * Determine whether a given page is eligible as a relocation destination.
 */
static __noinline bool
vm_phys_defrag_page_free(vm_page_t p)
{
        return (p->order == 0);
}

/*
 * Determine whether a given page is eligible to be relocated.
 * A suitable page is left in a xbusied state and its object is locked.
 */
static __noinline bool
vm_phys_defrag_page_relocatable(vm_page_t p)
{
	vm_object_t obj;

	if (p->order != VM_NFREEORDER || vm_page_wired(p) ||
	    (obj = atomic_load_ptr(&p->object)) == NULL)
		return false;

	VM_OBJECT_WLOCK(obj);
	if (obj != p->object || (obj->type != OBJT_DEFAULT && obj->type != OBJT_VNODE)) {
		goto unlock;
	}

  if (vm_page_tryxbusy(p) == 0)
		goto unlock;

	if (!vm_page_wired(p)) {
		return true;
	}

	vm_page_xunbusy(p);
unlock:
	VM_OBJECT_WUNLOCK(obj);
	return false;
}

/*
 * Tries to move 'src' into 'dst'.
 * Returns 0 on success, 1 if the error was caused by the src page, 2 if caused
 * by the dst page.
 */
static __noinline int
vm_phys_relocate_page(vm_page_t src, vm_page_t dst, int domain)
{
	int error = 0;
	struct vm_domain *vmd = VM_DOMAIN(domain);
	vm_object_t obj = src->object;

	vm_page_assert_xbusied(src);

	VM_OBJECT_ASSERT_WLOCKED(obj);
	KASSERT(vm_page_domain(src) == domain,
	    ("Source page is from a different domain"));
	KASSERT(vm_page_domain(dst) == domain,
	    ("Destination page is from a different domain"));

	vm_domain_free_lock(vmd);
	/* Check if the dst page is still eligible and remove it from the
	 * freelist. */
	if (dst->order == 0 || !vm_page_none_valid(dst)) {
		error = 2;
		vm_page_xunbusy(src);
		vm_domain_free_unlock(vmd);
		goto unlock;
	}


	vm_page_dequeue(dst);
	vm_phys_unfree_page(dst);
	vm_domain_free_unlock(vmd);
	vm_domain_freecnt_inc(vmd, -1);

	/* Unmap src page */
	if (obj->ref_count != 0 && !vm_page_try_remove_all(src)) {
		error = 1;

		vm_page_xunbusy(src);
		/* Place dst page back on the freelists. */
		vm_domain_free_lock(vmd);
		vm_phys_free_pages(dst, 0);
		vm_domain_free_unlock(vmd);
		vm_domain_freecnt_inc(vmd, 1);
		goto unlock;
	}
	/* Note - if this is missing the calling process gets stuck at the
	 * 'vmpfw' channel */
	if (dst->busy_lock == VPB_FREED) {
		dst->busy_lock = VPB_UNBUSIED;
	}

	/* Copy page attributes */
	dst->a.flags = src->a.flags & ~PGA_QUEUE_STATE_MASK;
	dst->oflags = 0;
	pmap_copy_page(src, dst);

	dst->valid = src->valid;
	dst->dirty = src->dirty;
	src->flags &= ~PG_ZERO;
	vm_page_dequeue(src);

	if (vm_page_replace_hold(dst, obj, src->pindex, src) &&
	    vm_page_free_prep(src)) {
		/* Return src page to freelist. */
		vm_domain_free_lock(vmd);
		vm_phys_free_pages(src, 0);
		vm_domain_free_unlock(vmd);

		vm_domain_freecnt_inc(vmd, 1);
	}

	vm_page_deactivate(dst);
unlock:
	VM_OBJECT_WUNLOCK(obj);

	return error;
}

static size_t
vm_phys_defrag(struct vm_compact_region_head *headp, int domain, void *p_data)
{
 vm_compact_region_t rp;
	size_t nrelocated = 0;
	int error;
  SLIST_FOREACH(rp, headp, entries){
          vm_page_t free = PHYS_TO_VM_PAGE(rp->start);
          vm_page_t scan = PHYS_TO_VM_PAGE(rp->end - PAGE_SIZE);

          KASSERT(free && scan, ("%s: pages are null %p, %p, start: %p, end: %p", __func__, free, scan, (void *)rp->start, (void *)rp->end));
          KASSERT(free->phys_addr && scan->phys_addr, ("%s: pages have null paddr %p, %p", __func__, (void *)free->phys_addr, (void*)scan->phys_addr));

          while (free < scan) {
                  /* Find suitable destination page ("hole"). */
                  while (free < scan && !vm_phys_defrag_page_free(free)) {
                          free++;
                  }

                  if (__predict_false(free >= scan)) {
                          break;
                  }

                  /* Find suitable relocation candidate. */
                  while (free < scan && !vm_phys_defrag_page_relocatable(scan)) {
                          scan--;
                  }

                  if (__predict_false(free >= scan)) {
                          break;
                  }

                  /* Swap the two pages and move "fingers". */
                  error = vm_phys_relocate_page(scan, free, domain);
                  if (error == 0) {
                          nrelocated++;
                          scan--;
                          free++;
                  } else if (error == 1) {
                          scan--;
                  } else {
                          free++;
                  }
          }
  }

	return nrelocated;
}


static struct proc *compactproc;
static struct thread *compact_threads[MAXMEMDOM - 1];

static void vm_phys_compact_thread(void *arg){
        void *cctx;
        size_t domain = (size_t)arg;
        void *chan = (void *)((vm_offset_t)vm_phys_compact_thread + domain);
        int error;

        vm_paddr_t start, end;

        start = vm_phys_search_index[domain].dom_start;
        end = vm_phys_search_index[domain].dom_end - PAGE_SIZE;
        cctx = vm_compact_create_job(vm_phys_compact_search, vm_phys_defrag,
                                     vm_phys_compact_ctx_init, start, end, 9, &error);
        KASSERT(cctx != NULL, ("Error creating compaction job: %d\n", error));

        for(;;){
                tsleep(chan, PPAUSE | PCATCH | PNOLOCK, "compact sleep", hz);
                kthread_suspend_check();
                vm_compact_run(cctx);
        }
        vm_compact_free_job(cctx);
}

static void vm_phys_compact_daemon(void){
        int error;

        for(size_t i=1; i< vm_ndomains; i++){
                error = kproc_kthread_add(vm_phys_compact_thread, (void *)i, &compactproc, &compact_threads[i-1], 0, 0, "compactdaemon", "compactdaemonthr%zu", i);
                if(error){
                        panic("%s: cannot start compaction thread, error: %d", __func__, error);
                }
        }

        printf("%s: compaction daemon started\n", __func__);
        vm_phys_compact_thread((void *)0);
}

static struct kproc_desc compact_kp = {
        "compactdaemon",
        vm_phys_compact_daemon,
        &compactproc
};
SYSINIT(compactdaemon, SI_SUB_KTHREAD_VM, SI_ORDER_ANY, kproc_start,
        &compact_kp);


static int sysctl_vm_phys_compact(SYSCTL_HANDLER_ARGS);
SYSCTL_OID(_vm, OID_AUTO, phys_compact, CTLTYPE_STRING | CTLFLAG_RD, NULL, 0,
    sysctl_vm_phys_compact, "A", "Compact physical memory");

static int
sysctl_vm_phys_compact(SYSCTL_HANDLER_ARGS)
{
	struct sbuf sbuf;
	int error;

	error = sysctl_wire_old_buffer(req, 0);
	if (error != 0)
		return (error);
	sbuf_new_for_sysctl(&sbuf, NULL, 32, req);

  for(int i=0; i < vm_ndomains; i++){
          void *chan = (void *)((vm_offset_t)vm_phys_compact_thread + i);
          wakeup_one(chan);
  }

	sbuf_printf(&sbuf, "Kicked compaction daemon\n");

	error = sbuf_finish(&sbuf);
	sbuf_delete(&sbuf);

	return (error);
}
