#ifndef ALLOCATE_H
#define ALLOCATE_H
/*
// Definitions for our handy ALLOCATE macros.
//
// Copyright © 1993, World Benders, Inc. All rights reserved.
*/

#define	ALLOCATE_ONE(the_type)			(the_type *) malloc (sizeof (the_type))
#define	ALLOCATE_SOME(n,the_type)		(the_type *) malloc (n * sizeof (the_type))
#define	ALLOCATE_CLEARED(n, the_type)	(the_type *) calloc (n, sizeof (the_type))
#define REALLOCATE(ptr, n, the_type)	(the_type *) realloc (ptr, n * sizeof (the_type))

#endif