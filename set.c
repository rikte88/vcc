/* Reference:		N. Wirth
 *			Algorithms + Data structures = Programs
 *			Section 4.4.6 Balanced Trees
 */

#include <string.h>
#include <stdlib.h>
#include <stdio.h>

typedef struct set_t	set_t;

struct set_t {
	set_t*		l;
	set_t*		r;
	void*		data;
	int		bal;
};


static void xdelete(set_t** , set_t* , void* , int* , int (*)(void*, void*));
set_t* new_set(void* data);

static void xadd(set_t** p, void* data, int* h, int (*cmp)(void*, void*))
{
	int			cond;
	set_t			*p1, *p2;

	if (*p == 0) {
		*p = new_set(data);
		*h = 1;
	} else  {
		cond = (*cmp)(data, (*p)->data);
		if (cond < 0) {
			xadd(&(*p)->l, data, h, cmp);
			if (*h) {
				/* left subtree has grown higher */
				switch((*p)->bal) {
				case 1:
					(*p)->bal = 0;
					*h = 0;
					break;
				case 0:
					(*p)->bal = -1;
					break;
				case -1:
					p1 = (*p)->l;
					if (p1->bal == -1) {
						/* single LL rotation */
						(*p)->l = p1->r;
						p1->r = *p;
						(*p)->bal = 0;
						*p = p1;
					} else {
						/* double LR rotation */
						p2 = p1->r;
						p1->r = p2->l;
						p2->l = p1;
						(*p)->l = p2->r;
						p2->r = *p;
						if (p2->bal == -1)
							(*p)->bal = 1;
						else
							(*p)->bal = 0;
						if (p2->bal == 1)
							p1->bal = -1;
						else
							p1->bal = 0;
						*p = p2;
					}
					(*p)->bal = 0;
					*h = 0;
				}
			}
		} else if (cond > 0) {
			xadd(&(*p)->r, data, h, cmp);
			if (*h) {
				/* right subtree has grown higher */
				switch ((*p)->bal) {
				case -1:
					(*p)->bal = 0;
					*h = 0;
					break;
				case 0:
					(*p)->bal = 1;
					break;
				case 1:
					p1 = (*p)->r;
					if (p1->bal == 1) {
						/* single RR rotation */
						(*p)->r = p1->l;
						p1->l = *p;
						(*p)->bal = 0;
						*p = p1;
					} else {
						/* double RL rotation */
						p2 = p1->l;
						p1->l = p2->r;
						p2->r = p1;
						(*p)->r = p2->l;
						p2->l = *p;
						if (p2->bal == 1)
							(*p)->bal = -1;
						else
							(*p)->bal = 0;
						if (p2->bal == -1)
							p1->bal = 1;
						else
							p1->bal = 0;
						*p = p2;
					}
					(*p)->bal = 0;
					*h = 0;
				}
			}
		}
	}
} 

void add(set_t** set, void* data, int (*cmp)(void*, void*))
{
	int			h;
	
	h = 0;
	if (*set == 0)
		*set = new_set(data);
	else
		xadd(set, data, &h, cmp);
}
	
	
void* find(set_t* p, void* data, int (*cmp)(void*, void*))
{
	int			cond;

	while (p != 0) {
		cond = (*cmp)(data, p->data);
		if (cond < 0)
			p = p->l;
		else if (cond > 0)
			p = p->r;
		else if (p->data == 0)
			return (void*)1;
		else
			return p->data;
	}

	return NULL;
}

static void l_bal(set_t** p, int* h)
{
	set_t			*p1, *p2;

	switch ((*p)->bal) {
	case -1:
		(*p)->bal = 0;
		break;
	case 0:
		(*p)->bal = 1;
		*h = 0;
		break;
	case 1:
		p1 = (*p)->r;
		if (p1->bal >= 0) {
			/* single RR rotation */
			(*p)->r = p1->l;
			p1->l = *p;
			if (p1->bal == 0) {
				(*p)->bal = 1;
				p1->bal = -1;
				*h = 0;
			} else {
				(*p)->bal = 0;
				p1->bal = 0;		
			} 
			*p = p1;
		} else {
			/* double RL rotation */
			p2 = p1->l;
			p1->l = p2->r;
			p2->r = p1;
			(*p)->r = p2->l;
			p2->l = *p;
			if (p2->bal == 1)
				(*p)->bal = -1;
			else 
				(*p)->bal = 0;
			if (p2->bal == -1)
				p1->bal = 1;	
			else 
				p1->bal = 0;

			*p = p2;
			p2->bal = 0;
		}
	}
}
	

static void r_bal(set_t** p, int* h)
{
	set_t			*p1, *p2;

	switch ((*p)->bal) {
	case 1:
		(*p)->bal = 0;
		break;
	case 0:
		(*p)->bal = -1;
		*h = 0;
		break;
	case -1:
		p1 = (*p)->l;
		if (p1->bal <= 0) {
			/* single LL rotation */
			(*p)->l = p1->r;
			p1->r = *p;
			if (p1->bal == 0) {
				(*p)->bal = -1;
				p1->bal = 1;
				*h = 0;
			} else {
				(*p)->bal = 0;
				p1->bal = 0;		
			} 
			*p = p1;
		} else {
			/* double LR rotation */
			p2 = p1->r;
			p1->r = p2->l;
			p2->l = p1;
			(*p)->l = p2->r;
			p2->r = *p;
			if (p2->bal == -1)
				(*p)->bal = 1;
			else 
				(*p)->bal = 0;
			if (p2->bal == 1)
				p1->bal = -1;	
			else 
				p1->bal = 0;

			*p = p2;
			p2->bal = 0;
		}
	}
}
	

void set_delete(set_t** set, void* data, int (*cmp)(void*, void*))
{
	int			h;
		
	h = 0;
	xdelete(set, 0, data, &h, cmp);
}

static void xset_free(set_t* p)
{
	if (p != 0) {
		xset_free(p->l);
		xset_free(p->r);
		free(p);
	}
}

void free_set(set_t** p)
{
	xset_free(*p);

	*p = NULL;
}

static void xset_size(set_t* p, size_t* n)
{
	if (p != NULL) {
		*n += 1;
		xset_size(p->l, n);
		xset_size(p->r, n);
	}
}

size_t set_size(set_t* p)
{
	size_t		n;

	n = 0;

	xset_size(p, &n);

	return n;
}

static void xfill_array(set_t* p, void*** a)
{
	if (p != 0) {
		xfill_array(p->l, a);
		*(*a)++ = p->data;
		xfill_array(p->r, a);
	}
}

void* set_to_array(set_t* p, size_t* n)
{
	void		**array;
	void		**a;

	*n = 0;

	xset_size(p, n);

	if (*n == 0)
		return 0;

	array = malloc(sizeof(void*) * *n);
	
	a = array;
	xfill_array(p, &a);
	
	return array;
}

static void del(set_t** r, set_t* q, int* h)
{
	set_t			*t;

	if ((*r)->r != 0) {
		del(&(*r)->r, q, h);
		if (*h)
			r_bal(r, h);
	} else {
		q->data = (*r)->data;
		t = *r;
		*r = (*r)->l;
		*h = 1;
		free(t);	
	}
}

static void xdelete(set_t** p, set_t* q, void* data, int* h, int (*cmp)(void*, void*))
{
	int			cond;

	if (*p == 0)
		;
	else {
		cond = (*cmp)(data, (*p)->data);
		if (cond < 0) {
			xdelete(&(*p)->l, q, data, h, cmp);
			if (*h)
				l_bal(p, h);
		} else if (cond > 0) {
			xdelete(&(*p)->r, q, data, h, cmp);
			if (*h)
				r_bal(p, h);
		} else {
			q = *p;
			if (q->r == 0) {
				*p = q->l;
				*h = 1;
				free(q);
			} else if (q->l == 0) {	
				*p = q->r;
				*h = 1;
				free(q);
			} else {
				del(&q->l, q, h);
				if (*h)
					l_bal(p, h);
			}
		}
	}
}

set_t* new_set(void* data)
{
	set_t		*set;

	set = malloc(sizeof(set_t));
	set->data	= data;
	set->l		= 0;
	set->r		= 0;
	set->bal	= 0;

	return set;
}

static int compare_address(void* a, void* b)
{
	return (char*)a - (char*)b;
}

void join_set(set_t** set, void* data)
{
	add(set, data, compare_address);
}

void leave_set(set_t** set, void* data)
{
	set_delete(set, data, compare_address);
}

unsigned in_set(set_t* set, void* data)
{
	return find(set, data, compare_address) != NULL;
}

void print_set(set_t* set, void (*fun)(void*, FILE*), FILE* fp)
{
	void**		a;
	size_t		n;
	size_t		i;

	a = set_to_array(set, &n);
	
	fprintf(fp, "{ ");
	for (i = 0; i < n; i += 1) {
		(*fun)(a[i], fp);
		if (i < n-1)
			fprintf(fp, ", ");
	}
	fprintf(fp, " }\n");
	fflush(fp);
	free(a);
}
