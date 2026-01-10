#ifndef LISP_LIKE_STUFF_H
#define LISP_LIKE_STUFF_H 1
/*
// Lisp-Like stuff in need of a neat name.
//
// Copyright 1993, 2004, Jonathan D. Callas. All Rights Reserved.
//
// 
*/

#ifndef MACINTOSH
#if defined(__MWERKS__) || defined (THINK_C) || defined (MPW)
#define MACINTOSH 1
#include <MacMemory.h>
#include <Resources.h>
#include <TextUtils.h>
#endif



#else
/* There'd need to be a way to distinguish Win32 from Unix here */
#define WIN32 0
#endif


#ifndef true
#define true 1
#endif



#ifndef false
#define false 0
#endif


#ifndef TRUE
#define TRUE true
#endif

#ifndef FALSE
#define FALSE false
#endif

#include <stdio.h>

#define LARGE_STRING 10000
#define SMALL_STRING 100

#define ALLOCATE_ONE(the_type)          (the_type *) malloc (sizeof (the_type))
#define ALLOCATE_SOME(n,the_type)       (the_type *) malloc (n * sizeof (the_type))
#define ALLOCATE_CLEARED(n, the_type)   (the_type *) calloc (n, sizeof (the_type))
#define REALLOCATE(ptr, n, the_type)    (the_type *) realloc (ptr, n * sizeof (the_type))
#define DEALLOCATE(ptr)                 free(ptr)

typedef enum
{
    PAIR_ATOM   = 'PAIR',
    INT_ATOM    = 'INTE',
    DBREF_ATOM  = 'DBRF',
    STRING_ATOM = 'STRN',
    SYMBOL_ATOM = 'SYMB',
    BASE64_ATOM = 'BS64',
    OBJECT_ATOM = 'OBJT',
    DEAD_ATOM   = 'DEAD'

} AtomTag;

typedef struct Atom
{
    union
    {
        long        number;
        struct 
        {
            struct Atom *first,
                        *rest;
        } pair;
        struct
        {
            char    *string;
            long    alloc_len,
                    current_len;
        } string;
        struct
        {
            void    *object;
            void    (*dispose_function)(void *);
        } object;
    } u;
    long            tag;
    long            refs;
} Atom;

#define TOKEN_DBREF         '%'
#define TOKEN_HEX           '#'

#define READING_INT         'rINT'
#define READING_DBREF       'rDBR'
#define READING_STRING      'rSTR'
#define READING_CANONSTRING 'rCST'
#define READING_SYMBOL      'rSYM'
#define READING_BASE64      'rB64'
#define READING_HEX         'rHEX'
#define READING_PAIR        'rPAI'
#define READING_CAPSULE     'rCAP'

#define READING_BEGIN       'rBEG'
#define READING_END         'rEND'
#define READING_ERROR       'rERR'
#define READING_WHITE       'rWHI'

#define READING_PLUS        'r+  '
#define READING_MINUS       'r-  '
#define READING_DBREF_TOKEN 'rDBT'
#define READING_DOT         'r.  '
#define READING_COMMA       'r,  '
#define READING_QUOTE       'rQUO'
#define READING_BACKQUOTE   'rBKQ'

#define SUBSTATE_NORMAL     'sNOR'
#define SUBSTATE_BSLASH     'sBSL'
#define SUBSTATE_QDIGIT     'sQdg'
#define SUBSTATE_DBREF      'sDBR'
#define SUBSTATE_MINUS      's-  '
#define SUBSTATE_PLUS       's+  '

#define WRITING_BEGIN       'wBEG'
#define WRITING_PAIR        'wPAI'
#define WRITING_SYMBOL      'wSYM'
#define WRITING_STRING      'wSTR'
#define WRITING_END         'wEND'
#define WRITING_BASE64      'wB64'
#define WRITING_ERROR       'wERR'

#define SUBSTATE_JUST_QUOTED 'wsJQ'

typedef struct AtomReader
{
    struct AtomReader *next,
                      *itsSupervisor;
    
    Atom    *head;
    Atom    *current;
    
    long    state,
            nextState,
            tempLong;
    long    thisChar;
    long    substate,
            negative;
} AtomReader;

#define MIN_LINE_LENGTH 40

typedef struct AtomWriter
{
    struct AtomWriter *next,
                      *itsSupervisor;
    
    Atom    *head;
    Atom    *current;

    Atom    *buffer;
    long    bufferLength;
    long    stringPos;
    long    howPretty;

    long    state;
    long    substate;
} AtomWriter;

#define llsNumber       u.number
#define llsFirst        u.pair.first
#define llsRest         u.pair.rest
#define llsString       u.string.string
#define llsStringSize   u.string.alloc_len
#define llsStringLen    u.string.current_len

#define PAIR_P(atom)    ((atom)->tag == PAIR_ATOM)
#define INT_P(atom)     ((atom)->tag == INT_ATOM)
#define INTEGER_P(atom) INT_P(atom)
#define DBREF_P(atom)   ((atom)->tag == DBREF_ATOM)
#define NUMBER_P(atom)  (INT_P(atom) || DBREF_P(atom))
#define STRING_P(atom)  ((atom)->tag == STRING_ATOM)
#define SYMBOL_P(atom)  ((atom)->tag == SYMBOL_ATOM)
#define BASE64_P(atom)  ((atom)->tag == BASE64_ATOM)
#define TEXT_P(atom)    (STRING_P(atom) || SYMBOL_P(atom) || BASE64_P(atom))
#define DEAD_P(atom)    ((atom)->tag == DEAD_ATOM)
#define OBJECT_P(atom)  ((atom)->tag == OBJECT_ATOM)
/* Note: This assumes PAIR_P. */
#define NIL(atom)       (!atom || (!atom->llsFirst && !atom->llsRest))

#define IS_VALID_ATOM(atom) (atom && (PAIR_P(atom) || NUMBER_P(atom) || TEXT_P(atom)))

#define LLS_CASE_UPPER  1
#define LLS_CASE_LOWER  2
#define LLS_CASE_CAP    3
#define LLS_CASE_CAPALL 4

Atom *create_int(long value);
Atom *create_dbref(long value);
AtomReader *create_reader(void);
Atom *create_pair(Atom *first, Atom *rest);
#define nil_pair() create_pair(NULL, NULL)

Atom *append_atom(Atom *to, Atom *from);
Atom *append_atom_char (Atom *a, char c);
Atom *append_atom_pstring(Atom *a, unsigned char *s);
Atom *append_atom_string(Atom *a, char *s);
Atom *aprintf(Atom *a, Atom *theAtom);
Atom *assoc_atom(Atom *obj, Atom *alist);
Atom *assocp_atom(Atom *obj, Atom *alist);
void beautify_atom(Atom *a);
Atom *assoc_prefix_atom(Atom *obj, Atom *alist);
Atom *case_convert_atom(Atom *string, int flag);
Atom *catenate_atoms(Atom *a, Atom *b);
void cleanup_atom(Atom *a);
void close_reader(AtomReader *ar);
Atom *copy_atom(Atom *a);
Atom *create_object(void *value, void (*df)(void *));
Atom *create_string(long size);
Atom *create_symbol(long size);
Atom *create_base64(long size);
AtomWriter *create_writer(Atom *theAtom, long lineLength, long howPretty);
Atom *deref_atom(Atom *a);
void dispose_atom(Atom *a);
void dispose_writer(AtomWriter *aw);
void dispose_reader(AtomReader *ar);
void dump_atom(Atom *a);
void dump_reader (AtomReader *ar);
Atom *dup_atom(Atom *a);
long equal_atom(Atom *a, Atom *b);
long equalp_atom(Atom *a, Atom *b);
long equal_prefix_atom(Atom *a, Atom *b);
#define feed_char(ar, c) _feed_char(ar, c, 0);
long _feed_char(AtomReader *ar, char c, int recursive);
Atom *first_atom(Atom *a);
Atom *format_atom(char *control, ...);
void fprint_atom(Atom *a, FILE *f);
long increase_atom_string(Atom *a, long to_add);
Atom *insert_atom_pstring(Atom *a, unsigned char *s, long position);
Atom *insert_atom_string(Atom *a, char *s, long position);
Atom *last_atom(Atom *a);
long length_atom(Atom *a);
Atom *list_ref(Atom *a, long n);
#if MACINTOSH
Atom *make_atom_handle(Handle h);
Atom *make_atom_IndString(short id, short index);
#endif
Atom *make_atom_pstring(unsigned char *s);
Atom *make_atom_psymbol(unsigned char *s);
Atom *make_atom_pbase64(unsigned char *s);
#if MACINTOSH
Atom *make_atom_STR(short id);
#endif
Atom *make_atom_string(char *s);
Atom *make_atom_symbol(char *s);
Atom *make_atom_base64(char *s);
Atom *make_list(Atom *a, ...);
Atom *make_object(void *value, void (*df)(void *));
Atom *member_atom(Atom *item, Atom *list);
Atom *memberp_atom(Atom *item, Atom *list);
Atom *member_prefix_atom(Atom *item, Atom *list);
long merge_lists (Atom *source, Atom **dest);
Atom *nconc_atom(Atom *to, Atom *from, long refFlag);
Atom *nconc_dbref(Atom *to, long n);
Atom *nconc_integer(Atom *to, long n);
Atom *nconc_string(Atom *to, char *string);
Atom *nconc_symbol(Atom *to, char *string);
char *next_writer_line(AtomWriter *aw);
Atom *nreverse_atom(Atom *a);
Atom *pop_atom(Atom **place);
void print_atom(Atom *a);
#define print_into(a, theAtom) _print_into(a, theAtom, 0)
Atom *_print_into(Atom *a, Atom *theAtom, long a_format);
Atom *push_atom(Atom *item, Atom **place);
Atom *reader_result(AtomReader *ar, int beGenerous);
Atom *read_atom(char **string);
AtomReader *read_from_string(AtomReader *ar, char **string);
AtomReader *read_from_binary_string(AtomReader *ar, char **string, long slen);
Atom *read_string(char *string);
Atom *read_atom_from_binary(char **string, long length);
Atom *ref_atom(Atom *a);
Atom *rest_atom(Atom *a);
Atom *reverse_atom(Atom *a);
Atom *setf(Atom **a, Atom *b);
Atom *set_atom_object(Atom *a, void *value, void (*df)(void *));
Atom *set_atom_string(Atom *a, char *s);
void base64_chunk(char *text, char *base64, int textCount);
#endif
