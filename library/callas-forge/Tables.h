/*
// Tables.h
// Copyright 1993, 2004, Jonathan D. Callas. All Rights Reserved.
//
*/

#ifndef TABLES_H
#define TABLES_H

#include "Lisp-Like-Stuff.h"

/*
////////////////////////////////////////////////////////////////////////////////
//
//	Generic table handling macros.			Exposed
//
//	These macros define the bulk of the public interface.
*/

#define	TABLE_CREATE(i)			(table_create (i))
#define	TABLE_LOOKUP(t, k)		(t ? ((t)->type->f_lookup) (t, k) : NULL)
#define	TABLE_ADD(t, k, v, o)	(t ? ((t)->type->f_add) (t, k, v, o) : FALSE)
#define	TABLE_SETF(t, k, a)		(t ? ((t)->type->f_setf) (t, k, a) : FALSE)
#define	TABLE_DELETE(t, k)		(t ? ((t)->type->f_delete) (t, k) : FALSE)
#define	TABLE_FREE_TABLE(t)		(t ? ((t)->type->f_free_table) (t) : FALSE)
#define	TABLE_FIRST(t, s)		(t ? ((t)->type->f_first) (t, &s) : NULL)
#define	TABLE_NEXT(t, s)		(t ? ((t)->type->f_next) (t, &s) : NULL)
#define	TABLE_COPY(tOld, tNew)	(table_copy (tOld, tNew))
#define TABLE_DUMP(t, f)		if (t) ((t)->type->f_dump) (t, f)

/*
// Where:
//		t = a pointer to a table	(tOld and tNew are, too)
//		k = a key, a string
//		v = a value to be stored in the datum field of the table entry
//		o = is the address of a void pointer (or NULL) to receive the old value
//		i = an unsigned integer threshold at which it ceases to be a LinkedList
//		s = a table_state, totally OPAQUE

//
//	Generic table data definitions
*/

struct table;

typedef	void *table_state;				/* Table state is OPAQUE */

typedef struct table_element			/* Table elements are exposed */
{
	char					*name;		/* Exposed */
	void					*datum;		/* Exposed */
	struct table_element	*next;		/* OPAQUE */
} table_element;

typedef struct table_class				/* Table class is OPAQUE */
{
	void			*(*f_lookup)	(struct table *, char *);
	int				 (*f_add)		(struct table *, char *, void *, void **);
	int				 (*f_setf)		(struct table *, char *, Atom *);
	int				 (*f_delete)	(struct table *, char *);
	int				 (*f_free_table)(struct table *);
	table_element	*(*f_first)		(struct table *, table_state *);
	table_element	*(*f_next)		(struct table *, table_state *);
	void			 (*f_dump)		(struct table *, FILE *);
} table_class;

typedef struct table					/* Table is OPAQUE */
{
	void			*header;
	table_class		*type;
	int				count;
} table;

/*
////////////////////////////////////////////////////////////////////////////////
//
//	Specific table creation prototypes		Exposed
*/

table	*linked_create (void);
table	*hashed_create (unsigned int size, unsigned int threshold);
table	*table_create (unsigned int threshold);

/*
////////////////////////////////////////////////////////////////////////////////
//
//	Generic table prototypes				Exposed
*/

int		table_copy (table *old_table, table *new_table);
#endif
