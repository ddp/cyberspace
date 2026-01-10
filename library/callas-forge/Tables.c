/* Tables.c
// Copyright 1993, 2004, Jonathan D. Callas. All Rights Reserved.

//
//	Tables.h and Tables.c define an object oriented generic table-handling system.
//	Methods/Function Members for handling the various operations are defined
//	as pointers to functions store in a prototypical class data structure.
//
//	Three types of tables are defined: LinkedLists, HashTables and the default
//	Table class which is a sub-class of LinkedList that will transform into a
//	HashTable if more than a specified number of entries are made in it.
//
//	The public interface to Tables.c is defined in Tables.h. Several things are
//	in fact exposed in Tables.h that in a more object oriented system would
//	not be. Only those elemenet defined as exposed in Tables.h should be accessed.
*/

#include "Lisp-Like-Stuff.h"
#include "Simple-Strings.h"
#include "Tables.h"

#include <stdlib.h>

/*
///////////////////////////////////////////////////////////////////////////////
//
//	Data structures for LinkedLists
*/

typedef struct linked_header
{
	table_element	*first;
	unsigned int	threshold;
} linked_header;

/*
//	linked prototypes
*/

static void				*linked_lookup (table *the_table, char *the_key);
static int				linked_add (table *the_table, char *the_key, void *the_value, void **old);
static int				linked_setf (table *the_table, char *the_key, Atom *the_atom);
static int				linked_delete (table *the_table, char *the_key);
static int				linked_free_linked (table *the_table);
static table_element	*linked_first (table *the_table, table_state *state);
static table_element	*linked_next (table *the_table, table_state *state);
static void				linked_dump (table *the_table, FILE *f);

/*
//	Function members of the LinkedList sub-class of generic tables
*/

static table_class linked_class_routines =
	{
		linked_lookup,
		linked_add,
		linked_setf,
		linked_delete,
		linked_free_linked,
		linked_first,
		linked_next,
		linked_dump
	};

/*
////////////////////////////////////////////////////////////////////////////////
//	Table prototypes
////////////////////////////////////////////////////////////////////////////////
*/

static int		table_add (table *the_table, char *the_key, void *the_value, void **old);
static int		table_setf (table *the_table, char *the_key, Atom *the_atom);

/*
//	Function members of the Table sub-class of LinkedList
*/

static table_class table_class_routines =
	{
		linked_lookup,
		table_add,			/* Special version that can convert to a HashTable */
		table_setf,			/* Special version that can convert to a HashTable */
		linked_delete,
		linked_free_linked,
		linked_first,
		linked_next,
		linked_dump
	};

/*///////////////////////////////////////////////////////////////////////////////
//
//	Data structures for HashTables
*/

typedef struct hashed_header
{
	unsigned int	size;
	unsigned int	threshold;
	table_element	*buckets[1];
} hashed_header;

/*
//	HashTable prototypes
*/

static unsigned int		hash (char *s, unsigned int size);
static int				rehash (table *the_table, unsigned int increment);

static void				*hashed_lookup (table *the_table, char *the_key);
static int				hashed_add (table *the_table, char *the_key, void *the_value, void **old);
static int				hashed_setf (table *the_table, char *the_key, Atom *the_atom);
static int				hashed_delete (table *the_table, char *the_key);
static int				hashed_free_hashed (table *the_table);
static table_element	*hashed_first (table *the_table, table_state *state);
static table_element	*hashed_next (table *the_table, table_state *state);
static void				hashed_dump (table *the_table, FILE *f);

/*
//	Function members of the HashTable sub-class of generic tables
*/

static table_class hashed_class_routines =
	{
		hashed_lookup,
		hashed_add,
		hashed_setf,
		hashed_delete,
		hashed_free_hashed,
		hashed_first,
		hashed_next,
		hashed_dump
	};

/*//////////////////////////////////////////////////////////////////////////////
//
//	A generic table-format independant routine for copying tables.
*/

int	table_copy (table *old_table, table *new_table)
{
	table_element	*x;
	table_state		state;
	
	for (x = TABLE_FIRST (old_table, state);
		 x;
		 x = TABLE_NEXT (old_table, state))
	{
		if (!TABLE_ADD (new_table, x->name, x->datum, NULL))
			return FALSE;
	}
	
	return TRUE;
}

/*//////////////////////////////////////////////////////////////////////////////
//
//	The actual default Table handling functions
//
//	The default table type is one that starts out as a LinkedList and becomes
//	a HashTable if its size exceeds a certain value.

//
//	Create a Table that starts as a LinkedList and becomes a HashTable.
*/

table *table_create (unsigned int threshold)
{
	table			*ptr;
	linked_header	*the_header;
	
	ptr = ALLOCATE_ONE (table);
	if (NULL == ptr)
		return ptr;

	the_header = ALLOCATE_ONE (linked_header);
	if (NULL == the_header)
	{
		DEALLOCATE (ptr);
		return NULL;
	}
	the_header->first = NULL;
	the_header->threshold = threshold;

	ptr->header = the_header;
	ptr->type = &table_class_routines;
	ptr->count = 0;
	
	return ptr;
}

/*
//	This routine is a specialized version of linked_add and should be kept in sync
*/

static int	table_add (table *the_table, char *the_key, void *the_value, void **old)
{
	table_element		*ptr;
	linked_header		*the_header;
	table				*new_table,
						 temp;	
	
	if (NULL == the_table)
		return FALSE;
	
	the_header = (linked_header *) the_table->header;
	if (NULL == the_header)
		return FALSE;

/*
//	If we're over the threshold, turn into a HashTable, and add to that.
*/
	if ((unsigned) the_table->count > the_header->threshold)
	{
		new_table = hashed_create (the_header->threshold, the_header->threshold);
		if (NULL == new_table)
			return FALSE;
				
		if (!table_copy (the_table, new_table))
		{
			TABLE_FREE_TABLE(new_table);
			return FALSE;
		}

/*
//	Swap the old and new tables
*/
		temp.header = the_table->header;
		temp.type = the_table->type;
		temp.count = the_table->count;
		
		the_table->header = new_table->header;
		the_table->type = new_table->type;
		the_table->count = new_table->count;
		
		new_table->header = temp.header;
		new_table->type = temp.type;
		new_table->count = temp.count;
		
		TABLE_FREE_TABLE(new_table);		/* This is actually the OLD table */
		
		return TABLE_ADD (the_table, the_key, the_value, old);
	}
/*
//	Otherwise just add to the LinkedList
*/	
	for (ptr = the_header->first; ptr; ptr = ptr->next)
		if (0 == string_compare (the_key, ptr->name))
			break;
			
	if (NULL == ptr)
	{
		ptr = ALLOCATE_ONE (table_element);
		if (NULL == ptr)
			return FALSE;
		ptr->name = dup_string (the_key);
		ptr->next = the_header->first;
		the_header->first = ptr;
		the_table->count++;
	}
	else
		if (NULL != old)
			*old = ptr->datum;
	
	ptr->datum = the_value;
	return TRUE;
}


/*
//	This routine is a specialized version of linked_setf and should be kept in sync
*/

static int	table_setf (table *the_table, char *the_key, Atom *the_atom)
{
	table_element		*ptr;
	linked_header		*the_header;
	table				*new_table,
						 temp;	
	
	if (NULL == the_table)
		return FALSE;
	
	the_header = (linked_header *) the_table->header;
	if (NULL == the_header)
		return FALSE;

/*
//	If we're over the threshold, turn into a HashTable, and setf to that.
*/
	if ((unsigned) the_table->count > the_header->threshold)
	{
		new_table = hashed_create (the_header->threshold, the_header->threshold);
		if (NULL == new_table)
			return FALSE;
				
		if (!table_copy (the_table, new_table))
		{
			TABLE_FREE_TABLE(new_table);
			return FALSE;
		}

/*
//	Swap the old and new tables
*/
		temp.header = the_table->header;
		temp.type = the_table->type;
		temp.count = the_table->count;
		
		the_table->header = new_table->header;
		the_table->type = new_table->type;
		the_table->count = new_table->count;
		
		new_table->header = temp.header;
		new_table->type = temp.type;
		new_table->count = temp.count;
		
		TABLE_FREE_TABLE(new_table);		/* This is actually the OLD table */
		
		return TABLE_SETF (the_table, the_key, the_atom);
	}
/*
//	Otherwise just add to the LinkedList
*/	
	for (ptr = the_header->first; ptr; ptr = ptr->next)
		if (0 == string_compare (the_key, ptr->name))
			break;
			
	if (NULL == ptr)
	{
		ptr = ALLOCATE_ONE (table_element);
		if (NULL == ptr)
			return FALSE;
		ptr->name = dup_string (the_key);
		ptr->next = the_header->first;
		the_header->first = ptr;
		the_table->count++;
	}
	
	setf ((Atom **) &ptr->datum, the_atom);
	return TRUE;
}


/*//////////////////////////////////////////////////////////////////////////////
//
//	Our LinkedList is a simple singly linked list stored with a string key
//	The keys are compared for a case-insensitive match. Case insensitivity
//	is based only on the 7-bit ASCII character set. A more rigorous scheme
//	is needed.

//
//	The actual LinkedList handling functions
*/

table *linked_create ()
{
	table			*ptr;
	linked_header	*the_header;
	
	ptr = ALLOCATE_ONE (table);
	if (NULL == ptr)
		return ptr;

	the_header = ALLOCATE_ONE (linked_header);
	if (NULL == the_header)
	{
		DEALLOCATE (ptr);
		return NULL;
	}
	the_header->first = NULL;
	the_header->threshold = 0xFFFFFFFF;	/* Not used, but there for Table compatibility */

	ptr->header = the_header;
	ptr->type = &linked_class_routines;
	ptr->count = 0;
	
	return ptr;
}

static void	*linked_lookup (table *the_table, char *the_key)
{
	table_element	*ptr;
	linked_header	*the_header;
	
	if (NULL == the_table)
		return NULL;
	
	the_header = (linked_header *) the_table->header;
	
	if (NULL == the_header)
		return NULL;
	
	for (ptr = the_header->first; ptr; ptr = ptr->next)
		if (0 == string_compare (the_key, ptr->name))
			return (ptr->datum);
	return NULL;
}

static int		linked_add (table *the_table, char *the_key, void *the_value, void **old)
{
	table_element	*ptr;
	linked_header	*the_header;
	
	if (NULL == the_table)
		return FALSE;
	
	the_header = (linked_header *) the_table->header;
	
	if (NULL == the_header)
		return FALSE;
	
	for (ptr = the_header->first; ptr; ptr = ptr->next)
		if (0 == string_compare (the_key, ptr->name))
			break;
			
	if (NULL == ptr)
	{
		ptr = ALLOCATE_ONE (table_element);
		if (NULL == ptr)
			return FALSE;
		ptr->name = dup_string (the_key);
		ptr->next = the_header->first;
		the_header->first = ptr;
		the_table->count++;
	}
	else
		if (NULL != old)
			*old = ptr->datum;
	
	ptr->datum = the_value;
	return TRUE;
}

static int		linked_setf (table *the_table, char *the_key, Atom *the_atom)
{
	table_element	*ptr;
	linked_header	*the_header;
	
	if (NULL == the_table)
		return FALSE;
	
	the_header = (linked_header *) the_table->header;
	
	if (NULL == the_header)
		return FALSE;
	
	for (ptr = the_header->first; ptr; ptr = ptr->next)
		if (0 == string_compare (the_key, ptr->name))
			break;
			
	if (NULL == ptr)
	{
		ptr = ALLOCATE_ONE (table_element);
		if (NULL == ptr)
			return FALSE;
		ptr->name = dup_string (the_key);
		ptr->next = the_header->first;
		the_header->first = ptr;
		the_table->count++;
	}
	
	setf ((Atom **) &ptr->datum, the_atom);
	return TRUE;
}

static int		linked_delete (table *the_table, char *the_key)
{
	table_element	*ptr,
					*last = NULL;
	linked_header	*the_header;
	
	if (NULL == the_table)
		return FALSE;
	
	the_header = (linked_header *) the_table->header;
	
	if (NULL == the_header)
		return FALSE;
	
	for (ptr = the_header->first; ptr; ptr = ptr->next)
	{
		if (0 == string_compare (the_key, ptr->name))
		{
			DEALLOCATE (ptr->name);
			if (last)
				last->next = ptr->next;
			else
				the_header->first = ptr->next;
			
			DEALLOCATE (ptr);
			the_table->count--;
			return TRUE;
		}
		last = ptr;
	}
	return FALSE;
}

static int		linked_free_linked (table *the_table)
{
	table_element	*ptr;
	linked_header	*the_header;
	
	if (NULL == the_table)
		return 0;
	
	the_header = (linked_header *) the_table->header;
	
	while ((ptr = the_header->first) != NULL)
	{
		the_header->first = ptr->next;
		DEALLOCATE (ptr->name);
		DEALLOCATE (ptr);
	}
	DEALLOCATE (the_table->header);
	DEALLOCATE (the_table);
	
	return 1;	
}

/*
//	The state for thses two routines consists of a pointer to the element AFTER the
//	element returned. The state is OPAQUE and may not be referenced by any routine
//	other than these two.
*/

static table_element	*linked_first (table *the_table, table_state *state)
{
	table_element	*ptr;
	linked_header	*the_header;
	
	if (NULL == the_table)
		return NULL;
	
	the_header = (linked_header *) the_table->header;
	
	if (NULL != (ptr = the_header->first))
	{
		* ((table_element **) state) = ptr->next;
		return ptr;	
	}

	* ((table_element **) state) = NULL;
	return (NULL);
}

#if 1
static table_element	*linked_next (table *the_table, table_state *state)
#else
static table_element	*linked_next (table *, table_state *state)
#endif
{
	table_element	*ptr;

	if (NULL != (ptr = *((table_element **) state)))	
	{
		* ((table_element **) state) = ptr->next;
		return ptr;		
	}

	return (NULL);
}

static void	linked_dump (table *the_table, FILE *f)
{
	table_element	*ptr;
	linked_header	*the_header;
	unsigned int	count = 0;
	
	if (NULL == the_table)
		return;
	
	the_header = (linked_header *) the_table->header;
	
	if (NULL == the_header)
		return;
	
	fprintf (f, "count: %d threshold: %d\n\n",
				the_table->count,
				the_header->threshold);

	for (ptr = the_header->first; ptr; ptr = ptr->next)
	{
		fprintf (f, "%6d: %s\n", ++count, ptr->name);
	}
}

/*
////////////////////////////////////////////////////////////////////////////////
//
//	The hashing algorythm here is pretty simple. A function hash() is called
//	to turn a string into a bucket number. This is done with a simple
//	x' = (x * 31) + n function, where n is first normalized so that upper-
//	and lower-case ASCII (seven bit) characters generate the same hash.
//
//	We may at some point want a more sophisticated hash, such as SNOBOL's
//	which generates not only the bucket number (which they call the 'bin')
//	but an 'ascension' as well, which is stored with the data element to
//	limit the number of string compares needed. Further, the string length
//	could be an additional tie-breaker. See p. 230 of Waite's "Implementing
//	Software for Non-Numeric Appliactions" for an example.
//
//	The bucket thus arrived at is a simple unsorted linked list. It is searched
//	sequentially for a string key which matches the requested key.

//
//	The actual HashTable handling functions
*/

table	*hashed_create (unsigned int size, unsigned int threshold)
{
	table			*ptr;
	hashed_header	*the_header;
	
	ptr = ALLOCATE_ONE (table);
	if (NULL == ptr)
		return ptr;

	the_header = (hashed_header	*) ALLOCATE_CLEARED (sizeof (hashed_header) + 
													 (size * sizeof (table_element *)),
								  					 char);
	if (NULL == the_header)
	{
		DEALLOCATE (ptr);
		return NULL;
	}

	the_header->size = size;
	the_header->threshold = threshold;

	ptr->header = the_header;
	ptr->type = &hashed_class_routines;
	ptr->count = 0;
	
	return ptr;
}

/*
// This handles upper and lower case ASCII characters the same, since it jams
// the 0x20 bit, which is the one that distinguishes case in the standard C1 sets.
// Apple's C2 set won't work the same way, but ISO Latin 1's will.
*/

static unsigned int hash(char *cp, unsigned int size)
{
	unsigned int sum = 0;

	while (cp != NULL && *cp != '\0')
		sum = DOWNCASE(*cp++) + (31 * sum);

	return sum % size;
}

static int	rehash (table *the_table, unsigned int increment)
{
	table_element	*ptr;
	hashed_header	*the_header,
					*new_header;
	table			*new_table;
	unsigned int	bucket,
					old_bucket;

	if (NULL == the_table)
		return FALSE;
	
	the_header = (hashed_header *) the_table->header;

	if (NULL == the_header)
		return FALSE;
	
	new_table = hashed_create (the_header->size + increment,
							   the_header->threshold);
	if (NULL != new_table)
	{
		new_header = (hashed_header *) new_table->header;
		for (old_bucket = 0; old_bucket < the_header->size; old_bucket++)
		{
			while ((ptr = the_header->buckets[old_bucket]) != NULL)
			{
				the_header->buckets[old_bucket] = ptr->next;	/* unlink from old */
				bucket = hash(ptr->name, new_header->size);		/* find new bucket */
				ptr->next = new_header->buckets[bucket];		/* and link it in */
				new_header->buckets[bucket] = ptr;				/*  to the new bucket */
				new_table->count++;								/* and up the count */
			}
		}
		DEALLOCATE (the_table->header);							/* Free the old header */
		the_table->header = new_table->header;					/* Copy the new table's */
		the_table->count = new_table->count;					/*   header and other */
		the_table->type = new_table->type;						/*   stuff over the old */
		DEALLOCATE (new_table);									/* and free the new table */
		return TRUE;
	}
	
	return FALSE;
}

static void	*hashed_lookup (table *the_table, char *the_key)
{
	table_element	*ptr;
	hashed_header	*the_header;
	unsigned int	count = 0;
	int				spike = FALSE;
	
	if (NULL == the_table)
		return NULL;
	
	the_header = (hashed_header *) the_table->header;
	
	if (NULL == the_header)
		return NULL;
	
	for (ptr = the_header->buckets[hash(the_key, the_header->size)];
		 ptr;
		 ptr = ptr->next)
	{
		if (count++ > (the_header->threshold + (the_header->threshold / 2)))
			spike = TRUE;

		if (0 == string_compare (the_key, ptr->name))
		{
			if (spike)
				rehash (the_table, 1);
			return (ptr->datum);
		}
	}

	if (spike)
		rehash (the_table, 1);
	return NULL;
}

static int		hashed_add (table *the_table, char *the_key, void *the_value, void **old)
{
	table_element	*ptr;
	hashed_header	*the_header;
	unsigned int	bucket;
	
	if (NULL == the_table)
		return FALSE;
	
	the_header = (hashed_header *) the_table->header;

	if (NULL == the_header)
		return FALSE;
	
	bucket = hash(the_key, the_header->size);
	for (ptr = the_header->buckets[bucket];
		 ptr;
		 ptr = ptr->next)
	{
		if (0 == string_compare (the_key, ptr->name))
			break;
	}

	if (NULL == ptr)
	{
		ptr = ALLOCATE_ONE (table_element);
		if (NULL == ptr)
			return FALSE;
		ptr->name = dup_string (the_key);
		ptr->next = the_header->buckets[bucket];
		the_header->buckets[bucket] = ptr;
		the_table->count++;
	}
	else
		if (NULL != old)
			*old = ptr->datum;
	
	ptr->datum = the_value;

/*
//	If we're over the threshold, rehash by doubling, more or less
*/
	if ((unsigned) (the_table->count * 2 ) > (the_header->threshold * the_header->size))
		rehash (the_table, the_header->size > 256 ? 256 : the_header->size);

	return TRUE;
}

static int		hashed_setf (table *the_table, char *the_key, Atom *the_atom)
{
	table_element	*ptr;
	hashed_header	*the_header;
	unsigned int	bucket;
	
	if (NULL == the_table)
		return FALSE;
	
	the_header = (hashed_header *) the_table->header;

	if (NULL == the_header)
		return FALSE;
	
	bucket = hash(the_key, the_header->size);
	for (ptr = the_header->buckets[bucket];
		 ptr;
		 ptr = ptr->next)
	{
		if (0 == string_compare (the_key, ptr->name))
			break;
	}

	if (NULL == ptr)
	{
		ptr = ALLOCATE_ONE (table_element);
		if (NULL == ptr)
			return FALSE;
		ptr->name = dup_string (the_key);
		ptr->next = the_header->buckets[bucket];
		the_header->buckets[bucket] = ptr;
		the_table->count++;
	}
	
	setf ((Atom **) &ptr->datum, the_atom);

/*
//	If we're over the threshold, rehash by doubling, more or less
*/
	if ((unsigned) (the_table->count * 2 ) > 

		(the_header->threshold * the_header->size))
		rehash (the_table, the_header->size > 256 ? 256 : the_header->size);

	return TRUE;
}

static int	hashed_delete (table *the_table, char *the_key)
{
	table_element	*ptr,
					*last = NULL;
	hashed_header	*the_header;
	unsigned int	bucket;
	
	if (NULL == the_table)
		return FALSE;
	
	the_header = (hashed_header *) the_table->header;
	
	if (NULL == the_header)
		return FALSE;
	
	bucket = hash(the_key, the_header->size);
	for (ptr = the_header->buckets[bucket];
		 ptr;
		 ptr = ptr->next)
	{
		if (0 == string_compare (the_key, ptr->name))
		{
			DEALLOCATE (ptr->name);
			if (last)
				last->next = ptr->next;
			else
				the_header->buckets[bucket] = ptr->next;
			
			DEALLOCATE (ptr);
			the_table->count--;
			return TRUE;
		}
		last = ptr;
	}
	return FALSE;
}

static int		hashed_free_hashed (table *the_table)
{
	table_element	*ptr;
	hashed_header	*the_header;
	unsigned int	bucket;
	
	if (NULL == the_table)
		return FALSE;
	
	the_header = (hashed_header *) the_table->header;
	
	for (bucket = 0;
		 bucket < the_header->size;
		 bucket++)
	{
		while ((ptr = the_header->buckets[bucket]) != NULL)
		{
			the_header->buckets[bucket] = ptr->next;
			DEALLOCATE (ptr->name);
			DEALLOCATE (ptr);
		}
	}
	DEALLOCATE (the_table->header);
	DEALLOCATE (the_table);
	
	return 1;
}

/*
//	The state for these two routines consists of an integer that gives the bucket
//	number and index within the bucket of the RETURNED element. The value of the
//	integer is (index * table_size) + bucket. The state is OPAQUE and may not be
//	referenced by any routine other than these two.
*/

static table_element	*hashed_first (table *the_table, table_state *state)
{
	table_element	*ptr;
	hashed_header	*the_header;
	unsigned int	size;
	unsigned int	bucket;
	
	if (NULL == the_table)
		return FALSE;
	
	the_header = (hashed_header *) the_table->header;
	size = the_header->size;
	
	for (bucket = 0; bucket < size; bucket++)
		if (NULL != (ptr = the_header->buckets[bucket]))
		{
			if (ptr->next)
				* ((unsigned int *) state) = bucket + size;
			else
				* ((unsigned int *) state) = bucket + 1;
			return ptr;	
		}

	* ((unsigned int *) state) = 0;
	return (NULL);
}

static table_element	*hashed_next (table *the_table, table_state *state)
{
	table_element	*ptr;
	hashed_header	*the_header;
	unsigned int	size;
	unsigned int	bucket;
	unsigned int	depth;
	unsigned int	i = 0;
	
	if (NULL == the_table
	 || 0 == *((unsigned int *) state))
		return FALSE;
	
	the_header = (hashed_header *) the_table->header;
	size = the_header->size;
	bucket = *((unsigned int *) state) % size;
	depth = *((unsigned int *) state) / size;
	
	for (ptr = the_header->buckets[bucket];
		 ptr;
		 ptr = ptr-> next)
	{
		if (i == depth)
		{
			if (ptr->next)
				* ((unsigned int *) state) = bucket + ((i + 1) * size);
			else
				* ((unsigned int *) state) = (bucket + 1) % size;
			return ptr;
		}
		i++;
	}

	for (bucket++; bucket < size; bucket++)
	{
		if (NULL != (ptr = the_header->buckets[bucket]))
		{
			if (ptr->next)
				* ((unsigned int *) state) = bucket + size;
			else
				* ((unsigned int *) state) = (bucket + 1) % size;
			return ptr;	
		}
	}

	* ((unsigned int *) state) = 0;
	return (NULL);
}

static void	hashed_dump (table *the_table, FILE *f)
{
	table_element	*ptr;
	hashed_header	*the_header;
	unsigned int	bucket;
	unsigned int	count;
	
	if (NULL == the_table)
		return;
	
	the_header = (hashed_header *) the_table->header;
	
	if (NULL == the_header)
		return;
	
	fprintf (f, "count: %d  buckets: %d  threshold: %d\n\n",
				the_table->count,
				the_header->size,
				the_header->threshold);

	for (bucket = 0; bucket < the_header->size; bucket++)
	{
		count = 0;
		for (ptr = the_header->buckets[bucket];
			 ptr;
			 ptr = ptr-> next)
		{
			fprintf (f, "%6d.%d: %s\n", bucket, ++count, ptr->name ? ptr->name : "wh¥¥ps");
		}
	}
}
