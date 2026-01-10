/*
// Lisp-Like stuff in need of a neat name.
//
// Copyright 1993, 2004, Jonathan D. Callas. All Rights Reserved.
//
// 
*/

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "Lisp-Like-Stuff.h"
#include "Simple-Strings.h"

extern char Base64Chars[];

/*

This is a package of data types and functions that give the features of
a Lisp/Scheme system, namely simple lists and relatives.

The major data type here is the "Atom." There are six types of Atoms,
integers, dbrefs, strings, symbols, and pairs.

Integers are a wrapper around a "long." DBREFs are a form of integer
that reference a database object in Meeting Space. They are always
printed as '%1234'. Note that while Meeting Space used the '#' character
to denote them, this version uses a constant to define what the token
character is to denote a DBREF.

Strings are a wrapper around C-strings (a.k.a. asciiz strings). These
strings are better than C-strings in that they resize for you when they
need to. When you print them, they also get double-quotes put around
them.

Symbols are simply a variant of strings. They are a word. Check the
reader for all the things that terminate a symbol.

Base64s are another variant of strings. They are a generic binary
string, quoted between two or-slash characters, '|', and base-64
encoded, with three binary bytes coded in three printable characters, as
per SPKI. Note that this really means that they are a different print
and read format for binary data, but are in all other respects a string.
Note also that since these may contain any binary data, assuming they
are null-terminated would be a mistake.

There is also another variant of Base64s, for SPKI use. These are
hexadecimal strings, quoted between '#' characters. This package reads
them in, and has options for printing them as described in the section
below for format_atom().

A pair is the basic building block of lists. It consists of two pointers
to other atoms, called "llsFirst" and "Rest." You can splice many of these
into a list by having the First pointer of each cell point to an atom of
the previous types (or a pair if you have nested lists), and the Rest
pointer point to the next pair. The last element should point to NULL,
*not* to a data-atom. If you're a lisp person, you know that this is a
dotted pair. The printer does print out dotted pairs correctly, and the
system *should* work correctly with them, but the reader does not read
dotted pairs, so don't do that. If you use read_string() to construct
your lists, then you don't have to worry about it. It won't make them.
Anyway, a list looks like this:

	(Foo "a string" 12)

+------+   +------+   +------+   
| Pair |   | Pair |   | Pair |   
|      |   |      |   |      |   
| R    |-->| R    |-->| R    |---> NULL
| F    |   | F    |   | F    |   
+------+   +------+   +------+   
   |          |          |      
   V          V          V      
+------+   +------+   +------+   
| Symb |   | Str  |   | Int  |   
|      |   |      |   |      |   
|"Foo" |   |"a..."|   | 12   |
+------+   +------+   +------+   

Another nice feature of these atoms is that they contain reference
counts in them, so that they can be copied by copying pointers and
deallocated when no longer used. It isn't a garbage collecter, but it's
still useful.

Think of the atoms containing these slots (or data members or whatever)

Atom->tag		--  The type of atom. Either PAIR_ATOM, INT_ATOM, 
                    DBREF_ATOM, STRING_ATOM, SYMBOL_ATOM, OBJECT_ATOM, 
                    BASE64_ATOM, DEAD_ATOM
					There are tag-checking macros PAIR_P(), INT_P(), 
                    INTEGER_P(), DEAD_P(), BASE64_P(), OBJECT_P(), 
                    DBREF_P(), STRING_P(), SYMBOL_P(), NUMBER_P(), and 
                    TEXT_P() -- text being string, symbol or base64, 
                    NUMBER being DBREF or integer, and INT and 
					INTEGER being synonyms.
					
                    Objects are an abstraction so that an arbitrary 
                    thing can be put in an atom it consists of an object 
                    value, and a dispose function. When the object atom 
                    is destroyed, the dispose function is called with 
                    the object value.
					
					Dead atoms exist solely so we can mark an atom thus 
                    when we delete it. This helps guard against double 
                    deallocations, and helps do the right thing should 
                    someone make a circular list, which they shouldn't, 
                    anyway.
					
Atom->refs		--  The reference count of this atom

Atom->llsNumber	--  The value of an INT_ATOM or DBREF_ATOM

Atom->llsFirst	--  The First (CAR) of a PAIR_ATOM
Atom->llsRest	--  The Rest (CDR) of a PAIR_ATOM

Atom->llsString	--  Pointer to a C-string. Don't save this away, it 
                    changes upon resize.
Atom->llsStringLen	
				--  The length of the string. It excludes the trailing 
                    null.
Atom->llsStringSize 
				-- The allocated length of the string buffer.

Here are the functions that let you manipulate atoms:

Atom *read_string(char *string)

	This function reads from the string and returns an Atom. If the
	string points to a list, then the whole list is returned. This
	corresponds to the Common Lisp function read-from-string.

Atom *read_atom(char **string)

	This function behaves much like read_string, but returns in "string"
	a pointer to the next character after the Atom it read. It varies in
	that read_atom doesn't convert the result to a string if it is not
	merely an atom.

Atom *read_atom_from_binary(char **string, long length)

	This function behaves like read_atom, but allows raw binary (like
	'\0') to be in the string, which would terminate read_atom or
	read_string.

Atom *setf(Atom **a, Atom *b)

	This function sets a (an atom-pointer passed by reference) to point
	to b, and returns a pointer to b. Conceptually,
	
		setf(&a, b)
		
	is the same as
	
		a = b;
	
	except for these neat features. The atom b (and all of its members,
	if it is a list), get their reference count increased. Also, the old
	value of a is dereferenced (and potentially deallocated) unless it
	is NULL, or already b. Thus setf(&a, a) does *not* add a reference
	to a, nor deallocate it. Ideally, you should use setf to set atom
	pointers.
	
	Please re-read the above paragraph. Note that setf() has an implicit
	deallocate in it. Because of this, you MUST MUST MUST MUST only setf
	into a pointer that holds an existing atom, or a NULL. If you don't,
	you'll get a weird-ass bus error.
	
	Example:
	
	Atom *list = NULL;
	
	setf(&list, read_string(string_buffer));

void dispose_atom(Atom *a)

	This function dereferences a and then deallocates all its pieces that
	end up with a zero or less reference count.
	
void cleanup_atom(Atom *a)

	This function does NOT dereference a, it ONLY deallocates the pieces
	that already have a zero (or less) reference count

Atom *ref_atom(Atom *a)

	Adds a reference to a and its submembers.
	
Atom *deref_atom(Atom *a)

	Removes a reference to a and its submembers. It does *not* deallocate
	memory.
	
Atom *create_int(long value)

	Creates an integer atom

Atom *create_dbref(long value)

	Creates an dbref atom

Atom *create_pair(Atom *first, Atom *rest)

	Creates a pair.
	
Atom *create_object(void *value, void (*df)(void *));
Atom *make_object(void *value, void (*df)(void *));

	Creates an object. They are synonyms; make calls create.
	
Atom *nil_pair()

	Shorthand for create_pair(NULL, NULL).

Atom *create_string(long size)

	Creates a string with an initial allocation of size.

Atom *create_symbol(long size)

	Creates a symbol with an initial allocation of size.

Atom *create_base64(long size)

	Creates a base64 string with an initial allocation of size.

Atom *make_atom_string(char *s)
Atom *make_atom_pstring(StringPtr s)
Atom *make_atom_symbol(char *s)
Atom *make_atom_psymbol(StringPtr s)

	returns an atom that is a string/symbol, made from either a C-string
	or P-string

Atom *make_atom_handle(Handle h)
Atom *make_atom_STR(short id)
Atom *make_atom_IndString(short id, short index)

	These routines make strings from Macintosh handles, STR resources,
	and STR# resources

long increase_atom_string(Atom *a, long to_add)

	Increases the size of String or Symbol. If the return value is zero,
	then there was a memory problem and it could not be increased.

void set_atom_string(Atom *a, char *s)

	Sets the value of a text atom to be a copy of the string supplied.

Atom *append_atom_string(Atom *a, char *s)
Atom *append_atom_pstring(Atom *a, unsigned char *s)

	Appends the string (or pascal string) to the text atom.
	
Atom *insert_atom_string(Atom *a, char *s, long position)

	Inserts the string into the text atom at the requested position. Zero
	is the start, any position after the end of the string is the end.

void append_atom_char(Atom *a, char *s)

	Appends the char to the text atom.

Atom *catenate_atoms(Atom *a, Atom *b)

	Appends the value of B to the value of A. Both are text. This is
	likely to be faster than using append_string_atom, so it should be
	used if possible. It returns the new length of A, or zero if there
	were memory problems.

Atom *case_convert_atom(Atom *string, int flag)

	Returns a new atom that is case coverted. Flag values are
	LLS_CASE_UPPER, LLS_CASE_LOWER, LLS_CASE_CAP, and LLS_CASE_CAPALL.

void dump_atom(Atom *a)

	Dumps an atom (or list) to stdout.
	
Atom *format_atom(char *control, ...)

	This returns a string atom that is constructed from the control
	string and the additional arguments. This intentionally resembles
	Common Lisp's FORMAT function, but isn't quite as advanced. It also
	resembles C's printf. The escape character is a ~ and the following
	formats are allowed:
	
		~~	--	inserts a ~
		~s	--	prints an atom reversably. Anything printed with ~s can 
                be read back in. This is also known as "s-expression" 
                format.
		~S  --  prints an atom in SPKI canonical form. Note that all 
                scalars in this format are converted to strings.
		~a	--	prints an atom in "asciified" format. Strings are 
                printed as-is and without any quoting.
		~i	--	prints a long integer in decimal radix.
		~d	--	prints a long integer as if it were a dbref.
		~x	--	prints a long integer in hexadecimal.
		~o	--	prints a long integer in octal.
		~c	--	prints the low byte of a long as a character.
		~t	--	prints a c-string.
		~p	--	prints a p-string.
		~r	--	prints a 'restype', a long integer used as 4 characters.
		~l	--	prints out a list as a comma separated sequence. For 
                example:
				(foo bar baz rag) becomes "foo, bar, baz, and rag". If 
                there are only two elements, it becomes "foo and bar". 
                If there is only one element, or this is a scalar, then 
                merely "foo". This uses ~s format.
		~L	--	Like ~l, but uses ~a format.
		~@l	--	prints one of a list. This takes two arguments, a list 
                and an index.
				It prints list_ref(list, i). Uses ~s format.
		~@L	--	Like ~@l but uses ~a format.
	
	You can also dispose the atom after using it with the formats ~s, ~S,
	~a, ~l, ~L, ~@l, and ~@L. You specify this with ~/s, ~/a, ~/l, ~/L,
	~@/l, and ~@/L.

Atom *print_into(Atom *a, Atom *theAtom)

	Appends a string representation of theAtom to the text a. In this
	function, symbols differ from strings in that strings have
	double-quotes put around them, and any internal double-quotes and
	backslashes are quoted by a backslash. Symbols are not quoted, and
	are just appended. If you have modified the contents of a symbol,
	then the printed representation may not be reversible. Symbols
	behave like ~a in Common Lisp's FORMAT, and strings behave like ~s.

Atom *aprintf(Atom *a, Atom *theAtom)

	Prints theAtom into string-atom a, overwriting what might be there.
	It uses print_into. The resulting string is returned. If you give
	NULL for a, then aprintf conjures a string for you.

void fprint_atom(Atom *a, FILE *f)
void print_atom(Atom *a)

	prints a string representation of a into FILE f (or stdout for
	print_atom()).

Atom *set_atom_object(Atom *a, void *value, void (*df)(void *))

	Sets the value or dispose function of an object. If either is NULL
	it won't be set.

Atom *list_ref(Atom *a, long n)

	Functions like the list-ref scheme function, n of 0 is the first
	item; returns NULL if the list is too short. Also returns NULL if a
	is not a pair.
	Example: 4th of (a b c d e f g h i) returns the e atom.

Atom *last_atom(Atom *a)
	Functions like the LAST lisp function. Returns the last PAIR in a 
    list.
	Returns a for non-pairs.
	Frequently what you will *really* want is 
    first_atom(last_atom(list))
	Example: LAST of (a b c d e f g h i) returns (i).
			 LAST of xyz returns xyz.

Atom *first_atom(Atom *a)
Atom *rest_atom(Atom *a)

	FIRST and REST. They return NULL for non-pairs.

Atom *copy_atom(Atom *a)

	Copies an atom or an entire list using dup_atom as a workhorse.

Atom *dup_atom(Atom *a)

	Copies a single atom. Dups of pairs have two NULL pointers. Dups of
	text have no extra space.

Atom *append_atom(Atom *to, Atom *from)

	Returns an atom that is a copy of from appended to a copy of to. 
    This mimics the Lisp APPEND function, but behaves sanely when given 
    non-pairs.
	Examples:
		Append[(a b c), (d e f)]	-> (a b c d e f)
		Append[12, "a string"]		-> (12 "a string")
		Append[(a b c), 12]			-> (a b c 12)
		Append[Alpha, (Beta Gamma)] -> (Alpha Beta Gamma)


Atom *nconc_atom(Atom *to, Atom *from, long refFlag)

	Appends to appended to from. This function destructively modifes the
	cells passed in to it, and adds pairs as needed to behave like
	append_atom() above! If refFlag is true, then the from cells will be
	referenced.

Atom *nconc_integer(Atom *to, long n)
Atom *nconc_dbref(Atom *to, long n)
Atom *nconc_string(Atom *to, char *string)
Atom *nconc_symbol(Atom *to, char *string)

	Creates the appropriate atom for the datum and sticks it on the end
	of the Atom, which should be a list, but will be dealt with if it
	isn't -- in which case you better use the returned pointer. The new
	item gets the same ref count as (last).

Atom *push_atom (Atom *item, Atom **place)

	Pushes the item into the list. If place isn't a pair, one is created
	and it becomes the First of it. Item gets attached to a pair, and
	both are referenced! This behaves mostly like the Common Lisp PUSH,
	but you can push onto a scalar.
	Examples:
		Push(12, (a b))				-> (12 a b)
		Push(12, 10)				-> (12 10)
		Push((a b), ((c d) (e f)))	-> ((a b) (c d) (e f))
		
	Best results are obtained by initializing your place to a NULL
	pointer or some suitable list.

Atom *pop_atom (Atom **place)

	Pops an item off of a list.
	Examples:
		Pop[(a b c)]				-> returns a, place is (b c)
		Pop[(a)]					-> returns a, place is NULL
		Pop[((a b) c d)]			-> returns (a b), place is (c d)
		Pop["Foo"]					-> returns "Foo", place is NULL
	
int	merge_lists (Atom *source, Atom **dest)

	Updates one association list from another. Items already in the
	destination list are updated. Those not already in it are pushed on.
	
	Examples:
	
		merge_lists (((a b) (c d)), ((a x) (y z)))	-> 
		((c d) (a b) (y z))
	
-------Readers and Writers-------

The following routines deal with objects called readers and writers.
Typically, you will never have to use a reader or writer yourself. The
read functions, for example, create a reader, use it, and dispose it.
However, if you find yourself needing to read in an atom piecemeal
(suppose you are reading it a character-at-a-time from a comm link),
then you might find it convenient to use a reader, as it contains all
the state necessary for making an atom.

There is one unfortunate gotcha in using a reader. Several atom types
know when they complete -- for example, a string is always terminated by
a double-quote, and a list always by a close-paren. However, a symbol
and a number are terminated by reading a character that is *not* part of
the element. This essentially requires you to have to know when your own
text terminates, and do the right thing. The right thing may be simply
feeding in a final CR, NL, or null, and then noting that the reader is
complete. It may also be that you call reader_result, and get the result
yourself. There's no easy answer, though, and you have to cope. My
apologies.

Note that if you are implicitly using a reader, you don't have to worry
about the above. It's all handled for you.

AtomReader *create_reader(void)

	This function creates an AtomReader, which is a block that can read
	characters one at a time building an extended atom. It is used by
	the read functions above.

AtomReader *read_from_string(AtomReader *reader char **string)

	This function reads from a string, into an AtomReader. If the pointer
	'reader' is NULL, then an AtomReader is created. Either 'reader' or
	the newly-created reader is returned, as applicable. The pointer
	'string' is returned pointing to the next unread character (or the
	string's terminating '\0').

AtomReader *read_from_binary_string(AtomReader *reader char **string, 
                                    long length)

	Like read_from_string, but works with known-length, binary strings.

long feed_char(AtomReader *reader, char c)

	This function feeds a character to the reader, accumulating it into
	the reader's atom. The result READER_ERROR indicates that something
	went awry, like you fed a character into a completed reader.
	
Atom *reader_result(AtomReader *reader, int beGenerous)

	This function returns the result of an atom reader. If beGenerous is
	true, then the reader gets closed out and its result returned. If
	beGenerous is false, then only a pending scalar value (like a
	string, symbol or number) will be closed. If there's a pending list,
	etc., then reader_result() returns NULL. The atom reader is always
	destroyed.

void close_reader(AtomReader *reader)

	This closes an open atom reader. The slot reader->head contains the
	accumulated atom.

void dispose_reader(AtomReader *reader)

	deallocates the reader and any associated structures.

void dump_reader(AtomReader *reader)

	dumps the state of the reader to stdout.

Reader states:

	The reader contains in it a state field, reader->state. There are a
	bunch of values possible. The important ones are READER_END, meaning
	that the reader has completed reading, and READER_ERROR, meaning
	that some error has occurred. Note that it is possible for a reader
	to not be complete, until it has been fed one more character than
	necessary. Both numbers and symbols can make this happen. The
	function reader_result() will close and return any pending value in
	the reader.


Writers:

A writer exists so that you can do something like take an
arbitrary-length atom, and write it out to a file that consists of
80-character lines. Later you might read these lines and use
read_from_string to reconstruct the atom, for example.

AtomWriter *create_writer(Atom *theAtom, long lineLength, 
                          long howPretty)

	This function creates an AtomWriter, which will print out the atom
	into lines for you. The supplied atom is copied into the writer, and
	you can continue to use your original copy. Currently, the parameter
	howPretty does nothing. Some day, we would like to incorporate a
	pretty-printer into the writer, but it's not there yet.

void dispose_writer(AtomWriter *aw)

	This function disposes of an AtomWriter and all its associated
	structures.

char *next_writer_line(AtomWriter *aw)

	This function returns the next line text representing the atom. It
	is an internal string of the writer -- you do not need to deallocate
	this. It returns a null string (first character is '\0') when
	complete. Also, when complete, the writer state is WRITER_END.

*/

Atom *setf(Atom **a, Atom *b)
{
	Atom	*old_a = *a;
	
	ref_atom(b);
	*a = b;

	dispose_atom(old_a);			/* deref and dispose of the old */
	
	return b;
}

Atom *ref_atom(Atom *a)
{
	if (a == NULL)
		return a;

	a->refs += 1;
	if (PAIR_P(a))
	{
		register Atom *b = a;
		
		if (b->llsFirst)
			ref_atom(b->llsFirst);

		while ((b = b->llsRest) != NULL)	/* Loop down the rests. */
		{
			b->refs += 1;
			if (!PAIR_P(b))
				break;
			else
				if (b->llsFirst)
					ref_atom(b->llsFirst);
		}
	}
	
	return a;
}

Atom *deref_atom(Atom *a)
{
	if (a == NULL)
		return a;

	a->refs -= 1;
	if (PAIR_P(a))
	{
		register Atom *b = a;
		
		if (b->llsFirst)
			deref_atom(b->llsFirst);

		while ((b = b->llsRest) != NULL)	/* Loop down the rests. */
		{
			b->refs -= 1;
			if (!PAIR_P(b))
				break;
			else
				if (b->llsFirst)
					deref_atom(b->llsFirst);
		}
	}
	
	return a;
}

Atom *create_int(long value)
{
	Atom *a  = ALLOCATE_CLEARED(1, Atom);
	if (a == NULL)
		return NULL;
	a->tag = INT_ATOM;
	a->llsNumber = value;
	return a;
}

Atom *create_dbref(long value)
{
	Atom *a = create_int(value);
	if (a != NULL)
		a->tag = DBREF_ATOM;
	return a;
}

Atom *create_pair(Atom *first, Atom *rest)
{
	Atom *a = ALLOCATE_CLEARED(1, Atom);
	if (a == NULL)
		return NULL;
	a->tag = PAIR_ATOM;
	a->llsFirst = first;
	a->llsRest = rest;
	
	return a;
}

Atom *create_string(long size)
{
	Atom *a = ALLOCATE_CLEARED(1, Atom);
	if (a == NULL)
		return NULL;
	a->tag = STRING_ATOM;
	a->llsString = ALLOCATE_SOME(size+1, char);
	if (a->llsString == NULL)
	{
		DEALLOCATE(a);
		return NULL;
	}
	a->llsString[0] = '\0';
	a->llsStringSize = size;
	a->llsStringLen = 0;
	
	return a;
}

Atom *create_symbol(long size)
{
	Atom *a = create_string(size);
	
	if (a != NULL)
		a->tag = SYMBOL_ATOM;

	return a;
}

Atom *create_base64(long size)
{
	Atom *a = create_string(size);
	
	if (a != NULL)
		a->tag = BASE64_ATOM;

	return a;
}

Atom *create_object(void *value, void (*df)(void *))
{
	Atom *a = ALLOCATE_CLEARED(1, Atom);
	if (a == NULL)
		return NULL;
	a->tag = OBJECT_ATOM;
	a->u.object.object = value;
	a->u.object.dispose_function = df;
	
	return a;
}

Atom *make_object(void *value, void (*df)(void *))
{
	return create_object(value, df);
}

Atom *set_atom_object(Atom *a, void *value, void (*df)(void *))
{
	if (a == NULL)
		return a;
	
	if (!OBJECT_P(a))
		return a;
	
	if (value != NULL)
		a->u.object.object = value;
	
	if (df != NULL)
		a->u.object.dispose_function = df;
	
	return a;
}

Atom *make_atom_string(char *s)
{
	Atom *a;
	
	if (s)
	{
		a = create_string(strlen(s) + 1);
		if (a)
			append_atom_string(a, s);
	}
	else
	{
		a = create_string(1);
	}
	
	return a;
}

Atom *make_atom_symbol(char *s)
{
	Atom *a;
	
	if (s)
	{
		a = create_symbol(strlen(s) + 1);
		if (a)
			append_atom_string(a, s);
	}
	else
	{
		a = create_symbol(1);
	}
	
	return a;
}

Atom *make_atom_base64(char *s)
{
	Atom *a;
	
	if (s)
	{
		a = create_base64(strlen(s) + 1);
		if (a)
			append_atom_string(a, s);
	}
	else
	{
		a = create_base64(1);
	}
	
	return a;
}

Atom *make_atom_pstring(unsigned char *s)
{
	Atom *a;
	
	if (s)
	{
		a = create_string(s[0] + 1);
		append_atom_pstring(a, s);
	}
	else
	{
		a = create_string(1);
	}
	
	
	return a;
}

Atom *make_atom_psymbol(unsigned char *s)
{
	Atom *a;
	
	if (s)
	{
		a = create_symbol(s[0] + 1);
		if (a)
			append_atom_pstring(a, s);
	}
	else
	{
		a = create_symbol(1);
	}
	
	return a;
}

Atom *make_atom_pbase64(unsigned char *s)
{
	Atom *a;
	
	if (s)
	{
		a = create_base64(s[0] + 1);
		if (a)
			append_atom_pstring(a, s);
	}
	else
	{
		a = create_base64(1);
	}
	
	return a;
}

#if MACINTOSH
Atom *make_atom_handle(Handle h)
{
	Atom *a;
	
	if (h)
	{
		a = create_string(GetHandleSize(h) + 1);
		if (a)
		{
			a->llsStringLen = a->llsStringSize - 1;
		
			HLock(h);
			BlockMove(*h, a->llsString, a->llsStringLen);
			HUnlock(h);
			a->llsString[a->llsStringLen] = '\0';
		}
	}
	else
	{
		a = create_string(1);
	}
	return a;
}

Atom *make_atom_STR(short id)
{
	Atom *a;
	StringHandle h = GetString(id);
	
	if (h)
	{
		HLock((Handle) h);
		a = make_atom_pstring(*h);
		ReleaseResource((Handle) h);
	}
	else
	{
		a = create_string(10);
	}
	
	return a;
}

Atom *make_atom_IndString(short id, short index)
{
	Str255 string;
	
	GetIndString(string, id, index);
	return make_atom_pstring(string);
}

#endif

long increase_atom_string(Atom *a, long to_add)
{
	long size = a->llsStringSize;
	char *newString;

	if (!TEXT_P(a))
		return 0;

	if (to_add <= 0)
	{
		if (size > LARGE_STRING)
			size += LARGE_STRING;
		else
		{
			if (size <= SMALL_STRING)
				size += SMALL_STRING;
			else
				size += size;
		}
	}
	else
		size += to_add;
		
	newString = ALLOCATE_SOME(size, char);
	if (newString == NULL)
	{
		return 0;
	}
#if MACINTOSH
	BlockMove(a->llsString, newString, a->llsStringSize);
#else
	memmove (newString, a->llsString, a->llsStringSize);
#endif

	a->llsStringSize = size;
	DEALLOCATE(a->llsString);
	a->llsString = newString;
	
	return size;
}

Atom *set_atom_string(Atom *a, char *s)
{
	a->llsStringLen = 0;
	
	return append_atom_string(a, s);
}

static Atom *insert_string(Atom *a, char *s, long length, long position)
{
	register long i;
	long allocated;
	register char *old, *t, *newStr;

	if (position < 0)
		position = 0;
	
	allocated = length + a->llsStringLen + 1;
	if (allocated < a->llsStringSize)
		allocated = a->llsStringSize;

	newStr = t = ALLOCATE_SOME(allocated, char);
	if (t)
	{
		old = a->llsString;
		
		for (i = 0; i < position; i++)
			*t++ = *old++;
		
		for (i = 0; i < length; i++)
			*t++ = *s++;
		
		while (*old)
			*t++ = *old++;
		
		*t = '\0';
		
		DEALLOCATE(a->llsString);
		a->llsString = newStr;
		a->llsStringLen += length;
		a->llsStringSize = allocated;
	}
	return a;
}

Atom *insert_atom_pstring(Atom *a, unsigned char *s, long position)
{
	if (s == NULL || *s == '\0')
		return a;
	
	if (position >= a->llsStringLen)
		return append_atom_pstring(a, s);
	
	return insert_string(a, (char *) &s[1], s[0], position);
}

Atom *insert_atom_string(Atom *a, char *s, long position)
{
	if (s == NULL || *s == '\0')
		return a;
	
	if (position >= a->llsStringLen)
		return append_atom_string(a, s);
	
	return insert_string(a, s, strlen(s), position);
}

Atom *append_atom_string(Atom *a, char *s)
{
	register long i, l;
	register char *t;
	
	if (s == NULL || *s == '\0')
		return a;
	
	i = a->llsStringLen;
	l = strlen(s) + 1;
	if (l < 8)
		l = 8;
	if (i + l >= a->llsStringSize)
	{
		if (increase_atom_string(a, l) == 0)
				return a;
	}
	
	t = a->llsString;

	while (*s)
	{
		t[i++] = *s++;
	}
	t[i] = '\0';
	
	a->llsStringLen = i;
	return a;
}

Atom *append_atom_pstring(Atom *a, unsigned char *s)
{
	register long i, l;
	register char *t;
	
	l = s[0];
	
	if (s == NULL || l == 0)
		return a;
	
	if (a->llsStringLen + l + 1 >= a->llsStringSize)
		if (increase_atom_string(a, l + 1) == 0)
			return a;
	
	t = a->llsString + a->llsStringLen;
	
	a->llsStringLen += l;
	
	for (i = 1; i <= l; i++)
	{
		*t++ = s[i];
	}
	
	*t = '\0';
	return a;
}

Atom *append_atom_char (Atom *a, char c)
{
	register long i, l;
	register char *t;
	
	i = a->llsStringLen;
	l = a->llsStringSize - 1;
	t = a->llsString;
	
	if (i >= l)
	{
		if (increase_atom_string(a, 0) == 0)
			return a;

		l = a->llsStringSize - 1;
		t = a->llsString;
	}
	
	t[i++] = c;

	t[i] = '\0';
	
	a->llsStringLen = i;
	return a;
}

Atom *catenate_atoms(Atom *a, Atom *b)
{
	register long i = b->llsStringLen + 1;
	/* Append the string in B to A. */
	
	if (a->llsStringSize <= (a->llsStringLen + i))
	{
		if (!increase_atom_string(a, i))
		return a;
	}
	
#if MACINTOSH
	BlockMove(b->llsString, &a->llsString[a->llsStringLen], i);
#else
	memcpy(b->llsString, &a->llsString[a->llsStringLen], i);
#endif
	a->llsStringLen += b->llsStringLen;

	return a;
}

Atom *case_convert_atom(Atom *string, int flag)
{
	Atom *newString = dup_atom(string);

	switch (flag)
	{
		case LLS_CASE_UPPER:
			lowerstring(newString->llsString);
			break;
			
		case LLS_CASE_LOWER:
			uppercase_string (newString->llsString);
			break;
			
		case LLS_CASE_CAP:
			capitalize(newString->llsString);
			break;
			
		case LLS_CASE_CAPALL:
			capitalize_string(newString->llsString);
			
		default:
			break;
	}	
	
	return newString;
}

void dump_atom(Atom *a)
{
	if (a == NULL)
	{
		printf("NIL (ptr)\n");
		return;
	}

	switch (a->tag)
	{
		case INT_ATOM:
			printf("INT (%ld) (%ld)\n", a->refs, a->llsNumber);
			break;
		case DBREF_ATOM:
			printf("DBREF (%ld) (%ld)\n", a->refs, a->llsNumber);
			break;
		case STRING_ATOM:
			printf("STRING (%ld) (%s)\n", a->refs, a->llsString);
			break;
		case SYMBOL_ATOM:
			printf("SYMBOL (%ld) (%s)\n", a->refs, a->llsString);
			break;
		case BASE64_ATOM:
		{
			Atom *text = format_atom("~s", a);
			printf("BASE64 (%ld) (%s)\n", a->refs, text->llsString);
			setf(&text, NULL);
			break;
		}
		case PAIR_ATOM:
			if (!a->llsFirst && !a->llsRest)
			{
				printf("PAIR (%ld) NIL\n", a->refs);
			}
			else
			{
				printf("PAIR (%ld) -> ", a->refs);
				dump_atom(a->llsFirst);
				dump_atom(a->llsRest);
			}
			break;
		default:
			printf("Unknown (%ld) (tag:%ld)\n", a->refs, a->tag);
			break;
	}
}

#if MEMORY_CHECK
static void refcheck(Atom *a)
{
	if (a->refs > 100 || a->refs < -10)
	{
		DebugStr("\pLotsa refs!");
	}
}
#endif

static void FREE_SIMPLE(Atom *atom)
{
	if (atom->tag == STRING_ATOM ||
	    atom->tag == SYMBOL_ATOM ||
	    atom->tag == BASE64_ATOM)
	{
		DEALLOCATE(atom->llsString);
		atom->llsString = NULL;
	}
	else if (atom->tag == OBJECT_ATOM &&
	         atom->u.object.dispose_function)
	{
		(*atom->u.object.dispose_function)
		    ((void *) atom->u.object.object);
	}
	atom->tag = DEAD_ATOM;
	DEALLOCATE(atom);
}


void dispose_atom(Atom *a)
{
	if (a == NULL)						/* Disposing nothing always */
		return;                         /*  works.                  */

	if (a->tag == DEAD_ATOM)			/* Double deallocation, or  */
		return;							/* circular list.           */
		                                /* Just cope with it.       */

#if MEMORY_CHECK
	refcheck(a);
#endif

	if (a->tag == PAIR_ATOM)			/* If it's a pair, walk     */
	{                                   /* down the backbone.       */
		Atom *b, *bnext;
		
		for (b = a; b; b = bnext)
		{
#if MEMORY_CHECK
			refcheck(b);
#endif
			if (b->tag == PAIR_ATOM)	/* get the next pointer     */
				bnext = b->llsRest;     /* now, we'll need it.      */
			else
				bnext = NULL;

			if (b->llsFirst)			/* Each item needs to be    */
			{							/* disposed, too.           */
			    /* This is only screwy for lists in lists, because  */
			    /* they need to be walked, too.                     */
			    
			    /* Recurse to get a sublist, but handle a scalar here.*/
				if (PAIR_P(b))
					dispose_atom(b->llsFirst);		
				else if (--(b->llsFirst->refs) <= 0)
				{
					FREE_SIMPLE(b->llsFirst);
				}
			}
			if (--(b->refs) <= 0)
			{
				FREE_SIMPLE(b);			/* get rid of this pair cell */
			}
		}

	}
	else if ( --(a->refs) <= 0)			/* Things not pairs are easy. */
	{
		FREE_SIMPLE(a);
	}
}

void cleanup_atom(Atom *a)
{
	if (a == NULL)
		return;

#if MEMORY_CHECK
	refcheck(a);
#endif

	if (a->tag == PAIR_ATOM)
	{
		Atom *b, *bnext;
		
		for (b = a; b; b = bnext)
		{
#if MEMORY_CHECK
			refcheck(b);
#endif
			if (b->tag == PAIR_ATOM)
				bnext = b->llsRest;
			else
				bnext = NULL;

			if (b->refs <= 0)
			{
				if (b->llsFirst)
					cleanup_atom(b->llsFirst);
				FREE_SIMPLE(b);
			}
			else
				bnext = NULL;
		}

	}
	else if (a->refs <= 0)
	{
		FREE_SIMPLE(a);
	}
}

#define CHECK_LEN(atom, needed, increase) \
	if ((atom)->llsStringSize <= ((atom)->llsStringLen + (needed))) \
		{ \
			if (!increase_atom_string(atom, (increase))) \
				return atom; \
		}

static void print_octal_quote(Atom *a, long c)
{
	char *s = &a->llsString[a->llsStringLen];
	sprintf(s, "\\%o", c & 0xffff);
	a->llsStringLen += strlen(s);
}

void base64_chunk(char *text, char *base64, int textCount)
{
	/* text is a string of up to 3 binary bytes.
	// base64 is a string of 4 text bytes that the base64 will be 
    //  written into.
    */
	
	switch (textCount)
	{
		case 3:
			base64[0] = Base64Chars[((text[0] >> 2) & 0x3f)];
			base64[1] = Base64Chars[((text[0] & 0x03) << 4) | 
			            ((text[1] >> 4) & 0x0f)];
			base64[2] = Base64Chars[((text[1] & 0x0f) << 2) | 
			            ((text[2] >> 6) & 0x03)];
			base64[3] = Base64Chars[(text[2] & 0x3f)];
			break;
		
		case 2:
			base64[3] = '=';
			base64[0] = Base64Chars[((text[0] >> 2) & 0x3f)];
			base64[1] = Base64Chars[((text[0] & 0x03) << 4) | 
			            ((text[1] >> 4) & 0x0f)];
			base64[2] = Base64Chars[((text[1] & 0x0f) << 2)];
			break;
			
		case 1:
			base64[3] = base64[2] = '=';
			base64[0] = Base64Chars[((text[0] >> 2) & 0x3f)];
			base64[1] = Base64Chars[((text[0] & 0x03) << 4)];
			break;
			
		default:
			base64[0] = base64[1] = base64[2] = base64[3] = '=';
			break;
	}
}

static Atom *canonical_print_into(Atom *a, Atom *theAtom)
{
	/* Append the value of theAtom to the string-atom A
	// This prints in "canonical form," which is strictly not 
    //    reversable.
	// It is not reversable because everything is turned into a 
    // canonical string, which will be read back as a string type. Also 
    // note that numbers are converted to strings here.
	*/
	
	if (theAtom == NULL) 
		return a;

	switch (theAtom->tag)
	{
		case BASE64_ATOM:
		case STRING_ATOM:
		case SYMBOL_ATOM:
		{
			CHECK_LEN(a, 12, 0);
			a->llsStringLen += sprintf(&a->llsString[a->llsStringLen], 
                                       "%ld", theAtom->llsStringLen);
			append_atom_char(a, ':');
			catenate_atoms(a, theAtom);
			break;
		}
		
		case INT_ATOM:
		case DBREF_ATOM:
		{
			char theInt[12];
			int  intLen;
			
			intLen = sprintf(theInt, "%ld", theAtom->llsNumber);
			a->llsStringLen += sprintf(&a->llsString[a->llsStringLen], 
                                       "%ld", intLen);
			append_atom_char(a, ':');
			append_atom_string(a, theInt);
			break;
		}
		
		case PAIR_ATOM:
			CHECK_LEN(a, 4, 0);
			a->llsString[a->llsStringLen++] = '(';
			{
				Atom *b;
				for (b = theAtom;b ; b = b->llsRest)
				{
					canonical_print_into(a, b->llsFirst);
				}
				CHECK_LEN(a, 2, 0);
				a->llsString[a->llsStringLen++] = ')';
				a->llsString[a->llsStringLen] = '\0';
			}
			break;
	}
	
	return a;	
}

static void hdprint(Atom *a, unsigned char hd)
{
	if (hd <= 9)
		append_atom_char(a, (char) ('0' + hd));
	else
		append_atom_char(a, (char) (('a' - 10) + hd));
}

static void hex_print(Atom *a, Atom *theAtom, long a_format)
{
	char *s = theAtom->llsString;
	int  slen = theAtom->llsStringLen, i;
	char high, low;

	if (!a_format)
		append_atom_char(a, '#');
			
	for (i = 0; i < slen; i++)
	{
		high = (s[i] >> 4) & 0x0f;
		low = s[i] &0x0f;
		
		hdprint(a, high);
		hdprint(a, low);
		
		if ((slen - i) > 1)
			append_atom_char(a, ' ');
	}

	if (!a_format)
		append_atom_char(a, '#');
}

Atom *_print_into(Atom *a, Atom *theAtom, long a_format)
{
	/* Append the value of theAtom to the string-atom A */
	
	long i;
	unsigned long c;
	long last_char_quoted = FALSE;

	if (theAtom == NULL) 
		return a;

	switch (theAtom->tag)
	{
		case BASE64_ATOM:
		{
			char *s = theAtom->llsString,
				 b[5];
			int  slen = theAtom->llsStringLen;
			
			if (slen <= 20)
			{
				hex_print(a, theAtom, a_format);
				break;
			}
			
			if (!a_format)
				append_atom_char(a, '|');
			
			b[4] = 0;
			while (slen >= 3)
			{
				base64_chunk(s, b, 3);
				append_atom_string(a, b);
				
				slen -= 3;
				s += 3;
			}
			
			if (slen)
			{
				/* At this point, note that there must be 1 or 2 
                // characters pending, because if it was an even 
                // multiple of 3, slen would be 0.
                */
				base64_chunk(s, b, slen);
				append_atom_string(a, b);
			}
			
			if (!a_format)
				append_atom_char(a, '|');
			break;
		}
		case STRING_ATOM:
		
			if (a_format)	/* print this string in a-format? */
			{
				catenate_atoms(a, theAtom);
				break;
			}

		/*** Yes!!! Fall through!!!! ***/	
		case SYMBOL_ATOM:
			i = theAtom->llsStringLen + 3;
			CHECK_LEN(a, i, i);

			if (STRING_P(theAtom))
				a->llsString[a->llsStringLen++] = '\"';
			
			for (i = 0; i < theAtom->llsStringLen; i++)
			{
				CHECK_LEN(a, 5, 0);
				c = theAtom->llsString[i] & 0xff;

				if (c == '\"' ||
					(c == '\\' && STRING_P(theAtom)))
				{
					a->llsString[a->llsStringLen++] = '\\';
					a->llsString[a->llsStringLen++] = (char)c;
				}
				else if (c == 0x7f || (c < 0x20 && c != '\t') || 
						 (last_char_quoted && c >= '0' && c <= '7'))
						 /* DEL, or C0 & not tab */

				{
					print_octal_quote(a, c);
					last_char_quoted = TRUE;
				}
				else
				{
					a->llsString[a->llsStringLen++] = (char)c;
					last_char_quoted = FALSE;
				}
			}

			if (theAtom->tag == STRING_ATOM)
				a->llsString[a->llsStringLen++] = '\"';

			a->llsString[a->llsStringLen] = '\0';
			break;
		
		case INT_ATOM:
			CHECK_LEN(a, 12, 0);

			a->llsStringLen += sprintf(&a->llsString[a->llsStringLen], 
                                       "%ld", theAtom->llsNumber);
			break;
			
		case DBREF_ATOM:
			CHECK_LEN(a, 14, 0);

			a->llsStringLen += sprintf(&a->llsString[a->llsStringLen], 
                                       "%c%ld", 
									   TOKEN_DBREF,
									   theAtom->llsNumber);
			break;
			
		case PAIR_ATOM:
			CHECK_LEN(a, 4, 0);
			a->llsString[a->llsStringLen++] = '(';
			{
				Atom *b;
				for (b = theAtom;b ; b = b->llsRest)
				{
					_print_into(a, b->llsFirst, a_format);

					if (b->llsRest)
					{
						CHECK_LEN(a, 4, 0);
						a->llsString[a->llsStringLen++] = ' ';
						if (b->llsRest->tag != PAIR_ATOM)
						{
							a->llsString[a->llsStringLen++] = '.';
							a->llsString[a->llsStringLen++] = ' ';
						}
					}
				}
				CHECK_LEN(a, 2, 0);
				a->llsString[a->llsStringLen++] = ')';
				a->llsString[a->llsStringLen] = '\0';
			}
			break;
	}
	return a;
}

Atom *aprintf(Atom *a, Atom *theAtom)
{
	/* Print theAtom into a, which is assumed to be a STRING_ATOM, 
	// or equivalent.
	*/
	
	if (a == NULL)
		a = create_string(SMALL_STRING);
	
	a->llsStringLen = 0;
	print_into(a, theAtom);
	return a;
}

#define grab_white(s) while (*s && isspace(*s)) s++

#ifdef OLD_READER

static long quoted_strlen(char *s)
{
	/* Pointer to a double-quoted string. Find its length. */
	long i = 0;
	s++;			/* Ignore initial quote. */
	
	while (*s && *s != '\"')
	{
		if (*s == '\\')
			s++;	/* Skip backslash */
			
		i++;
		s++;
	}
	
	return i;
}

static long symbol_strlen(char *s)
{
	/* Pointer to a symbol. Find its length. */
	long i = 0;

	while (*s && !isspace(*s) && *s != ')')
	{
		i++;
		s++;
	}
	return i;
}

Atom *old_read_atom(char **string)
{
	Atom *a;
	char *s = *string;

	if (NULL == s  || *s == '\0')
		return NULL;
	else if (*s == '(')
	{
		Atom *b;
		s++;
		grab_white(s);
		
		a = create_pair(NULL, NULL);
		if (a == NULL)
			return NULL;
		b = a;
		
		while (*s && *s != ')')
		{
			b->llsFirst = old_read_atom(&s);
			
			if (*s != ')' && *s != '\0')
			{
				b->llsRest = create_pair(NULL, NULL);
				if (b->llsRest == NULL)
				{
					dispose_atom(a);
					return NULL;
				}
				b = b->llsRest;
			}
			if (b == NULL)		/* Belated check for memory failure */
				break;
		}
		if (*s) s++;
	}
	else if (*s == '\"')
	{
		long i, l;
		char *t;

		l = quoted_strlen(s);

		a = create_string(l + 1);
		if (a == NULL)
			return NULL;

		t = a->llsString;		
		a->llsStringLen = l;
		
		s++;							/* Skip past quote */
		
		for (i = 0; i < l; i++)
		{
			if (*s == '\\')
				s++;
			*t++ = *s++;
		}
		*t = '\0';
		if (*s) s++;					/* Skip past quote */
	}
	else if (isdigit(*s) || 
			 ((*s == '-') && (isdigit(s[1]))) || 
			 ((*s == '+') && (isdigit(s[1]))) || 
			 ((*s == TOKEN_DBREF) && (isdigit(s[1]))))
			 /* A number? */
	{
		long negative = FALSE;
		
		if (*s == TOKEN_DBREF)
		{
			a = create_dbref(0);
			s++;
		}
		else
			a = create_int(0);

		if (a == NULL)
			return NULL;
		
		/* figure out the sign. Be liberal. */
		while (*s == '-' || *s == '+')	
		{
			if (*s++ == '-')
				negative = !negative;
		}
		
		grab_white(s);
		
		while (isdigit(*s))		/* compute the number */
		{
			a->llsNumber = (a->llsNumber *10) + (*s++ - '0');
		}
		
		if (negative)
			a->llsNumber = -a->llsNumber;
	}
	else			/* Symbol -- a "single-word" string */
	{
		long i, l;
		char *t;

		l = symbol_strlen(s);
		a = create_symbol(l + 1);
		if (a == NULL)
			return NULL;

		a->llsStringLen = l;
		t = a->llsString;
		a->tag = SYMBOL_ATOM;

		for (i = 0; i < l; i++)
		{
			*t++ = *s++;
		}
		*t = '\0';
	}
	
	grab_white(s);
	*string = s;
	return a;
}

#endif		/* OLD_READER */

Atom *read_string(char *string)
{
	Atom *head;
	char *s = string;
	
	grab_white(s);
	
	head = read_atom(&s);
	
	grab_white(s);
	
	if (*s != '\0')
	{	/* Stupid parse error -- redo the string as a string. */
		dispose_atom(head);
		head = make_atom_string(string);
	}

	return head;
}

Atom *list_ref(Atom *a, long n)
{
	/* Functions like the list-ref Scheme function, n of 0 is the first 
    // item; returns NULL if the list is too short.
	//
	// Example: 4th of (a b c d e f g h i) returns the e atom.
	*/
	
	register Atom *b = a;
	register long i = n;
	
	if (!PAIR_P(b))
		return NULL;
	
	while (b && i-- > 0)
	{
		if (!PAIR_P(b))
			b = NULL;

		if (b)
			b = b->llsRest;
	}
	
	return b ? b->llsFirst : NULL;
}

Atom *last_atom(Atom *a)
{
	/* Like the LAST lisp function. Returns the last PAIR in a list.
	//
	// Example: LAST of (a b c d e f g h i) returns (i).
	//			LAST of xyz returns xyz.
	*/
	
	register Atom *b = a;

	while (b && b->tag == PAIR_ATOM && b->llsRest)
	{
		b = b->llsRest;
	}
	
	return b;
}

Atom *first_atom(Atom *a)
{
	/* Like FIRST (a.k.a. CAR)
	*/
	
	if (a && a->tag == PAIR_ATOM)
		return a->llsFirst;
	else
		return NULL;
}

Atom *rest_atom(Atom *a)
{
	/* Like REST (a.k.a. CDR)
	*/
	
	if (a && a->tag == PAIR_ATOM)
		return a->llsRest;
	else
		return NULL;
}

void print_atom(Atom *a)
{
	fprint_atom(a, stdout);
}

void fprint_atom(Atom *a, FILE *f)
{
	Atom *str = create_string(100);
	if (str == NULL)
	{
		fputs("***Memory-error-in-fprint_atom***\n", f);
	}
	else
	{
		aprintf(str, a);
	
		fputs(str->llsString, f);
		fputs("\n", f);
	}
	dispose_atom(str);
}

Atom *dup_atom(Atom *a)
{
	/* Shallowest of shallow copies. Duplicates the one atom.
	// Dups of PAIRs are NIL.
	// Dups of STRINGs/SYMBOLs have no extra space.
	*/
	
	Atom *dup;
	
	if (a == NULL)
		return NULL;
	
	switch (a->tag)
	{
		case INT_ATOM:
			dup = create_int(a->llsNumber);
			break;
		case DBREF_ATOM:
			dup = create_dbref(a->llsNumber);
			break;
		case PAIR_ATOM:
			dup = nil_pair();
			break;
		case SYMBOL_ATOM:
		case STRING_ATOM:
		case BASE64_ATOM:
			dup = create_string(a->llsStringLen + 1);
			if (dup == NULL)
				break;
#if MACINTOSH
			BlockMove(a->llsString, dup->llsString, 
			          a->llsStringLen + 1);
#else
			memmove(dup->llsString, a->llsString, a->llsStringLen + 1);
#endif
			dup->llsStringLen = a->llsStringLen;
			dup->llsStringSize = dup->llsStringLen + 1;
			dup->tag = a->tag;
			break;
	}
	
	return dup;
}

Atom *copy_atom(Atom *a)
{
	/* Deep copy. Copies the whole shebang. */
	
	Atom *dup = dup_atom(a);
	
	if (dup == NULL)
		return NULL;
	
	if (a->tag == PAIR_ATOM)
	{
		Atom *b = a, *bdup = dup;
		
		while (a)
		{
			bdup->llsFirst = copy_atom(b->llsFirst);
			if (bdup->llsFirst == NULL && b->llsFirst != NULL)
			{
				dispose_atom(bdup);
				return NULL;
			}
			
			if (b->llsRest != NULL)
			{
				bdup->llsRest = dup_atom(b->llsRest);
				if (bdup->llsRest == NULL)
				{
					dispose_atom(bdup);
					return NULL;
				}
				if (b->llsRest->tag == PAIR_ATOM)
				{
					b = b->llsRest;
					bdup = bdup->llsRest;
				}
			}
			else
				break;
		}
	}
	return dup;
}

Atom *append_atom(Atom *to, Atom *from)
{
	Atom *newTo, *newFrom, *tail;
	
	if (to->tag == PAIR_ATOM)
		newTo = copy_atom(to);
	else
		newTo = create_pair(copy_atom(to), NULL);
	
	if (from->tag == PAIR_ATOM)
		newFrom = copy_atom(from);
	else
		newFrom = create_pair(copy_atom(from), NULL);
	
	if (newTo == NULL || newFrom == NULL)
	{
		dispose_atom(newTo);
		dispose_atom(newFrom);
		return NULL;
	}
	
	tail = last_atom(newTo);

	if (tail->llsRest == NULL)
		tail->llsRest = newFrom;
	else
	{
		/* Jeez, a dotted pair! */
		
		tail->llsRest = create_pair(tail->llsRest, newFrom);
	}
	return newTo;
}

Atom *nconc_atom(Atom *to, Atom *from, long refFlag)
{
	Atom *newAtom, *tail;

	if (to->tag != PAIR_ATOM)		/* Arrgh! Modify in place.      */
	{
		newAtom = ALLOCATE_SOME(1, Atom);
		if (newAtom == NULL)
			return NULL;
		*newAtom = *to;				/* Copy the cell.               */
		to->tag = PAIR_ATOM;		/* Transmogrify to into a PAIR. */
		to->llsFirst = newAtom;
		to->llsRest = NULL;
	}

	if (from->tag != PAIR_ATOM)		/* Arrgh! Modify in place.      */
	{
		newAtom = ALLOCATE_SOME(1, Atom);
		if (newAtom == NULL)
			return NULL;
		*newAtom = *from;			/*  Copy the cell.              */
		from->tag = PAIR_ATOM;		/* Transmogrify from into a PAIR. */
		from->llsFirst = newAtom;
		from->llsRest = NULL;
	}
	
	tail = last_atom(to);
	
	if (tail->llsRest == NULL)
		tail->llsRest = from;
	else
	{
		/* Jeez, a dotted pair! */
		newAtom = ALLOCATE_SOME(1, Atom);
		if (newAtom == NULL)
			return NULL;
		*newAtom = 	*tail->llsRest;
		tail->llsRest->tag = PAIR_ATOM;	/* Transmogrify tail->llsRest 
                                            into a PAIR. */
		tail->llsRest->llsFirst = newAtom;
		tail->llsRest->llsRest = NULL;
	}
	
	if (refFlag)
		ref_atom(from);

	return to;
}

Atom *push_atom(Atom *item, Atom **place)
{
	Atom *pair = NULL;
	
	if (item == NULL)		/* Is this null? */
		return *place;		/* Just return.. */

	if (*place == NULL)		/* Pushing onto a null list? */
	{
		setf(&pair, create_pair(item, NULL));	/* Create a pair and 
                                                    reference it. */
		*place = pair;
		return pair;
	}
	else
	{
		if (!PAIR_P(*place))
		{
			pair = create_pair(item, NULL);	/* Make a pair          */
			if (pair == NULL)				/* bail if no memory    */
				return *place;
			
			pair->refs = item->refs;		/* Ref'ed as much as the */
			*place = pair;					/* atom. change place   */
                                            /* and continue below.  */
		}
		
		if ((*place)->llsFirst == NULL)		/* Is this a NIL pair?  */
		{
			(*place)->llsFirst = item;		/* splice it in.        */
			item->refs += (*place)->refs;	/* add in the extra     */
                                            /* references.          */
		}
		else
		{
			pair = create_pair(item, NULL);	/* Make a pair          */
			if (pair == NULL)				/* bail if no memory    */
				return *place;
			
			ref_atom(pair);					/* The item has a new   */
                                            /* reference.           */
			pair->llsRest = *place;			/* Splice the rest of   */
			                                /* the list.            */
			*place = pair;					/* Return and leave.    */
		}
	}
	return *place;
}

Atom *pop_atom(Atom **place)
{
	Atom *item, *junk;
	
	if (NULL == place || NULL == *place)
		return NULL;
	
	if (PAIR_P(*place))
	{
		junk = *place;
		*place = junk->llsRest;
		item = junk->llsFirst;
		junk->refs--;
		if (junk->refs <= 0)
		{
			junk->llsFirst = NULL;
			junk->llsRest = NULL;
			dispose_atom(junk);
		}
	}
	else
	{
		item = *place;
		*place = NULL;
	}
	
	return deref_atom(item);
}

long length_atom(Atom *a)
{
	long i;

	if (a == NULL)
		return 0;
	else if (PAIR_P(a))
	{
		i = 0;
		if (a->llsFirst == NULL && a->llsRest == NULL)
			return 0;
		
		while (a != NULL)
		{
			i++;
			a = a->llsRest;
		}

		return i;
	}
	else
		return -1;
}

long equal_atom(Atom *a, Atom *b)
{
	if (a == b)
		return 1;
	
	if (!a || !b || (a->tag != b->tag))
		return 0;
	
	switch (a->tag)
	{
		case INT_ATOM:
		case DBREF_ATOM:
			return a->llsNumber == b->llsNumber;

		case STRING_ATOM:
		case SYMBOL_ATOM:
		case BASE64_ATOM:
			return !strcmp(a->llsString, b->llsString);
		
		case PAIR_ATOM:
			return	equal_atom(a->llsFirst, b->llsFirst) &&
					equal_atom(a->llsRest, b->llsRest);
		
		default:
			return FALSE;
	}
}

long equalp_atom(Atom *a, Atom *b)
{
	if (a == b)
		return 1;
	
	if (!a || !b)
		return 0;
	
	if (a->tag != b->tag)
	{
		if (!((NUMBER_P(a) && NUMBER_P(b)) ||
			  (TEXT_P(a) && TEXT_P(b))))
			return 0;
	}
	
	switch (a->tag)
	{
		case INT_ATOM:
		case DBREF_ATOM:
			return a->llsNumber == b->llsNumber;

		case STRING_ATOM:
		case SYMBOL_ATOM:
		case BASE64_ATOM:
			return !string_compare(a->llsString, b->llsString);

		case PAIR_ATOM:
			return	equalp_atom(a->llsFirst, b->llsFirst) &&
					equalp_atom(a->llsRest, b->llsRest);
		
		default:
			return FALSE;
	}
}

long equal_prefix_atom(Atom *a, Atom *b)
{
	if (a == b)
		return 1;
	
	if (!a || !b)
		return 0;
	
	if (a->tag != b->tag)
	{
		if (!NUMBER_P(a) || !NUMBER_P(b))
			return 0;
	}
	
	switch (a->tag)
	{
		case INT_ATOM:
		case DBREF_ATOM:
			return a->llsNumber == b->llsNumber;

		case STRING_ATOM:
		case SYMBOL_ATOM:
		case BASE64_ATOM:
			return string_prefix(a->llsString, b->llsString);

		case PAIR_ATOM:
			return	equalp_atom(a->llsFirst, b->llsFirst) &&
					equalp_atom(a->llsRest, b->llsRest);
		
		default:
			return FALSE;
	}
}

Atom *assoc_atom(Atom *obj, Atom *alist)
{
	Atom *a;
	
	if (!alist || !PAIR_P(alist))
		return NULL;
	
	for (a = alist; a && PAIR_P (a); a = a->llsRest)
	{
		if (a->llsFirst != NULL
		 && PAIR_P (a->llsFirst)
		 && equal_atom(obj, a->llsFirst->llsFirst))
			return a->llsFirst;
	}
	
	return NULL;
}

Atom *assocp_atom(Atom *obj, Atom *alist)
{
	Atom *a;
	
	if (!alist || !PAIR_P(alist))
		return NULL;
	
	for (a = alist; a && PAIR_P (a); a = a->llsRest)
	{
		if (a->llsFirst != NULL
		 && PAIR_P (a->llsFirst)
		 && equalp_atom(obj, a->llsFirst->llsFirst))
			return a->llsFirst;
	}
	
	return NULL;
}

Atom *assoc_prefix_atom(Atom *obj, Atom *alist)
{
	Atom *a;
	
	if (!alist || !PAIR_P(alist))
		return NULL;
	
	for (a = alist; a && PAIR_P (a); a = a->llsRest)
	{
		if (a->llsFirst != NULL
		 && PAIR_P (a->llsFirst)
		 && equal_prefix_atom(a->llsFirst->llsFirst, obj))
			return a->llsFirst;
	}
	
	return NULL;
}

static Atom *pairify(Atom *to)
{
	if (!PAIR_P(to))
	{
		to = create_pair(to, NULL);
		if (to)
			to->refs = to->llsFirst->refs;
	}
	return to;
}

static Atom *unsplice_dotted_pair(Atom *theLast)
{
	if (theLast->llsRest != NULL)		/* Damned dotted pair? */
	{
		theLast->llsRest = create_pair(theLast->llsRest, NULL);
		if (theLast->llsRest)
		{
			theLast->llsRest->refs = theLast->refs;
			theLast = theLast->llsRest;
		}
	}
	return theLast;	
}

Atom *nconc_integer(Atom *to, long n)
{
	Atom *theLast;
	
	to = pairify(to);
	theLast = unsplice_dotted_pair(last_atom(to));

	theLast->llsRest = create_pair(create_int(n), NULL);
	
	return to;
}

Atom *nconc_dbref(Atom *to, long n)
{
	Atom *theLast;
	
	to = pairify(to);
	theLast = unsplice_dotted_pair(last_atom(to));

	theLast->llsRest = create_pair(create_dbref(n), NULL);
	
	return to;
}

Atom *nconc_string(Atom *to, char *string)
{
	Atom *theLast;
	
	to = pairify(to);
	theLast = unsplice_dotted_pair(last_atom(to));

	theLast->llsRest = create_pair(create_string(strlen(string)), NULL);
	set_atom_string(theLast->llsRest->llsFirst, string);
	
	return to;
}

Atom *nconc_symbol(Atom *to, char *string)
{
	Atom *theLast;
	
	to = pairify(to);
	theLast = unsplice_dotted_pair(last_atom(to));

	theLast->llsRest = create_pair(create_symbol(strlen(string)), NULL);
	set_atom_string(theLast->llsRest->llsFirst, string);
	
	return to;
}

long merge_lists (Atom *source, Atom **dest)
{
	Atom	*it,
			*the_atom;

	if (source && PAIR_P (source))
	{
		for (it = source; it; it = it->llsRest)
		{
			if (PAIR_P (it->llsFirst))
			{
				if (NULL == (the_atom = 
				    assocp_atom (it->llsFirst->llsFirst, *dest)))
				{
					push_atom (copy_atom(it->llsFirst), dest);
				}
				else
				{
					setf (&(the_atom->llsRest), it->llsFirst->llsRest);
				}
			}
		}
		return 1;
	}
	else
		return 1;
}

Atom *nreverse_atom(Atom *a)
{
	Atom *spot = NULL, *i;
	
	if (NULL == a || (!PAIR_P(a)))
		return a;
	
	while (a)
	{
		i = a;				/* Grab first item          */
		a = a->llsRest;		/* Cut it from the list     */
		
		if (!PAIR_P(i))		/* Not a pair?              */
		{
			i = pairify(i);	/* pair it.                 */
			a = NULL;		/* Don't hack up the list   */
		}

		i->llsRest = spot;	/* place it in the new list */
		spot = i;
	}
	
	return spot;
}

Atom *reverse_atom(Atom *a)
{
	return nreverse_atom(copy_atom(a));
}

Atom *member_atom(Atom *item, Atom *list)
{
	Atom *i;

	if ((NULL == item) || (NULL == list))
		return NULL;
	
	if (!PAIR_P(list))
	{
		if (equal_atom(list, item))
			return list;
		else
			return NULL;
	}
	
	for (i = list; i; i = i->llsRest)
	{
		if (equal_atom(i->llsFirst, item))
			return i;
	}
	
	return NULL;
}

Atom *memberp_atom(Atom *item, Atom *list)
{
	Atom *i;

	if ((NULL == item) || (NULL == list))
		return NULL;
	
	if (!PAIR_P(list))
	{
		if (equalp_atom(list, item))
			return list;
		else
			return NULL;
	}
	
	for (i = list; i; i = i->llsRest)
	{
		if (equalp_atom(i->llsFirst, item))
			return i;
	}
	
	return NULL;
}

Atom *member_prefix_atom(Atom *item, Atom *list)
{
	Atom *i;

	if ((NULL == item) || (NULL == list))
		return NULL;
	
	if (!PAIR_P(list))
	{
		if (equal_prefix_atom(list, item))
			return list;
		else
			return NULL;
	}
	
	for (i = list; i; i = i->llsRest)
	{
		if (equal_prefix_atom(i->llsFirst, item))
			return i;
	}
	
	return NULL;
}

Atom *make_list(Atom *a, ...)
{
	Atom *the_list, *current, *next;
	
	va_list ap;
	
	the_list = create_pair(a, NULL);
	if (the_list == NULL)
		return NULL;
	current = the_list;
	
	va_start(ap, a);
	
	while (NULL != (next = va_arg(ap, Atom *)))
	{
		current->llsRest = create_pair(next, NULL);
		if (current->llsRest == NULL)
		{
			dispose_atom(the_list);
			return NULL;
		}
		current = current->llsRest;
	}
	
	va_end(ap);
	
	return the_list;
}

Atom *format_atom(char *control, ...)
{
	Atom *result, *a;
	char *s = control;
	char format, 
		 at_sign = FALSE,
		 slash = FALSE;
	long i;

	va_list ap;
	
	if (s == NULL)
		return NULL;
	
	result = create_string(100);
	if (result == NULL)
		return NULL;

	va_start(ap, control);
	
	while (*s)
	{
		if (*s != '~')						/* Not a tilde? Copy.   */
		{
			CHECK_LEN(result, 2, SMALL_STRING);
			result->llsString[result->llsStringLen++] = *s;
			result->llsString[result->llsStringLen] = '\0';
		}
		else								/* Format types...      */
		{
			format = *++s;					/* Get format character */
			if (format == '@')
			{
				at_sign = TRUE;
				format = *++s;
			}
			
			if (format == '/')
			{
				slash = TRUE;
				format = *++s;
			}
			
			switch (format)
			{
				case '~':
					append_atom_char(result, format);
					break;

				case 's':
					a = va_arg(ap, Atom *);
					if (IS_VALID_ATOM(a))
					{
						print_into(result, a);
						if (slash)
							dispose_atom(a);
					}
					break;
				
				case 'S':
					a = va_arg(ap, Atom *);
					if (IS_VALID_ATOM(a))
					{
						canonical_print_into(result, a);
						if (slash)
							dispose_atom(a);
					}
					break;

				case 'a':
					a = va_arg(ap, Atom *);
					if (IS_VALID_ATOM(a))
					{
						_print_into(result, a, 1);	/* use A-format. */
						if (slash)
							dispose_atom(a);
					}
					break;

				case 'c':
					append_atom_char(result, 
					                 (char)(va_arg(ap, long) & 0xff));
					break;

				case 'i':
				case 'd':
				case 'x':
				case 'o':
				{
					char buf[16], subcontrol[4];
					
					i = va_arg(ap, long);
					subcontrol[0] = '%';
					subcontrol[1] = 'd';
					if (format == 'x' || format == 'o')
						subcontrol[1] = format;
					subcontrol[2] = '\0';

					sprintf(buf, subcontrol, i);
					if (format == 'd')
						append_atom_char(result, TOKEN_DBREF);
					append_atom_string(result, buf);
					
					break;
				}
				
				case 't':
					append_atom_string(result, va_arg(ap, char *));
					break;
				
				case 'p':
				{
#if MACINTOSH
					if (at_sign)
					{
						long resource = va_arg(ap, long);
						long index = va_arg(ap, long);
						Atom *indStr = make_atom_IndString(resource, index);
						catenate_atoms(result, indStr);
						dispose_atom(indStr);
					}
					else
						append_atom_pstring(result, va_arg(ap, unsigned 
                                            char *));
#else
					append_atom_pstring(result, va_arg(ap, unsigned char 
                                        *));
#endif
					break;
				}
				
				case 'r':		/* A 'ABCD' type. A 4-char longword. */
				{
					CHECK_LEN(result, 5, SMALL_STRING);
					restype_to_chars(va_arg(ap, long), 
							&result->llsString[result->llsStringLen]);
					result->llsStringLen += 4;
					result->llsString[result->llsStringLen] = '\0';
					break;
				}
				case 'l':
				case 'L':
				{
					a = va_arg(ap, Atom *);
					if (at_sign)
					{
						i = va_arg(ap, long);
						if (IS_VALID_ATOM(a))
						{
							a = list_ref(a,i);
							if (IS_VALID_ATOM(a))
							{
								_print_into(result, a, format == 'L');
							}
						}
					}
					else
					{
						i = length_atom(a);
						switch (i)
						{
							case 0:	/* scalar, print it. */
								_print_into(result, a, format == 'L');
								break;
								
							case 1:	/* List length 1, just print it. */
								_print_into(result, a->llsFirst, 
								            format == 'L');
								break;
							
							case 2:	/* List length 2 -> FOO and BAR */
								_print_into(result, a->llsFirst, 
								            format == 'L');
								append_atom_string(result, " and ");
								_print_into(result, 
                                            a->llsRest->llsFirst, 
                                            format == 'L');
								break;
							
							default: /* List longer than 2 -> 
							            FOO, BAR, BAZ, and RAG */
							{
								Atom *item;
								
								_print_into(result, a->llsFirst, 
								            format == 'L');

								for (item = a->llsRest; item; 
								     item = item->llsRest)
								{
									append_atom_string(result, ", ");
									if (item->llsRest == NULL)
										append_atom_string(result, 
										                   "and ");
									_print_into(result, 
									            item->llsFirst, 
									            format == 'L');
								}
							}
						}
					}
					if (slash)
						dispose_atom(a);
					break;
				}
			}
			at_sign = FALSE;
			slash = FALSE;
		}
		
		s++;
	}
	
	va_end(ap);
	
	return result;
}

void beautify_atom(Atom *a)
{
	Atom *b;
	int i;
	char *s;
	
	switch(a->tag)
	{
		case SYMBOL_ATOM:
		case STRING_ATOM:
			s = a->llsString;
			
			for (i = 0; i < a->llsStringLen; i++)
			{
				if (!isgraph(s[i]))
				{
					a->tag = BASE64_ATOM;
					break;
				}
			}
			break;
		
		case PAIR_ATOM:
		{
			b = a;
			while(b)
			{
				beautify_atom(b->llsFirst);
				b = b->llsRest;
			}
		}
		
		default:
			break;
	}
}

