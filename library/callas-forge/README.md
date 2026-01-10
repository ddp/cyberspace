# Lisp-Like-Stuff

**Author:** Jonathan D. Callas
**Copyright:** 1993, 2004
**Provenance:** Digital Equipment Corporation era

---

## Overview

A complete S-expression system implemented in C, with native support for SPKI syntax. This package provides the fundamental data types and operations of Lisp/Scheme: atoms, pairs, lists, reader, writer, and the classic list-processing primitives.

## Historical Significance

This code was written by Jon Callas during the formative years of SPKI/SDSI development. It demonstrates how S-expressions can be efficiently implemented in C while maintaining the elegance of Lisp-style data manipulation.

Key features that made this relevant to SPKI:
- Native base64 encoding (between `|` delimiters)
- Hexadecimal binary strings (between `#` delimiters)
- Reference-counted memory management
- Clean reader/writer architecture

## Files

| File | Purpose |
|------|---------|
| `Lisp-Like-Stuff.c` | Core implementation (~1400 lines) |
| `Lisp-Like-Stuff.h` | Data structures and API |
| `Atom-Reader.c` | S-expression parser |
| `Simple-Strings.c/h` | String utilities |
| `Tables.c/h` | Lookup tables (base64, etc.) |
| `Allocate.h` | Memory allocation macros |

## Data Types

```
Atom Types:
  PAIR_ATOM   - Cons cell (first, rest)
  INT_ATOM    - Long integer
  DBREF_ATOM  - Database reference (%1234)
  STRING_ATOM - Quoted string ("...")
  SYMBOL_ATOM - Unquoted symbol
  BASE64_ATOM - Binary data (|...|)
  OBJECT_ATOM - Arbitrary C object wrapper
```

## Key Functions

```c
// Reading
Atom *read_string(char *string);
Atom *read_atom(char **string);

// Writing
void print_atom(Atom *a);
Atom *format_atom(char *control, ...);

// List operations
Atom *first_atom(Atom *a);      // CAR
Atom *rest_atom(Atom *a);       // CDR
Atom *create_pair(Atom *first, Atom *rest);  // CONS
Atom *nconc_atom(Atom *to, Atom *from, long refFlag);
Atom *reverse_atom(Atom *a);
Atom *copy_atom(Atom *a);

// Association lists
Atom *assoc_atom(Atom *obj, Atom *alist);
Atom *member_atom(Atom *item, Atom *list);

// Memory management
Atom *ref_atom(Atom *a);        // Increment refcount
void dispose_atom(Atom *a);     // Decrement refcount
```

## Example Usage

```c
// Parse an SPKI certificate
Atom *cert = read_string("(cert (issuer |base64key|) (subject alice))");

// Navigate the structure
Atom *issuer = assoc_atom(make_atom_symbol("issuer"), cert);
Atom *key = first_atom(rest_atom(issuer));

// Build a response
Atom *response = make_list(
    make_atom_symbol("ack"),
    copy_atom(key),
    NULL);

print_atom(response);
// Output: (ack |base64key|)
```

## Design Notes

From the source documentation:

> "This is a package of data types and functions that give the features of
> a Lisp/Scheme system, namely simple lists and relatives."

The code uses reference counting rather than garbage collection - pragmatic for C integration while preventing most memory leaks.

## License

From ReadMe.txt:

> "You have license to adapt or use this in your software provided that you put in some reasonable place a credit that you are using Jon Callas's Multi-Lingual Password Generator."

> "I believe that open source should be open. I'm not a fan of the GPL and other restrictive licenses."

## About the Author

Jon Callas - University of Maryland (Mathematics), cryptographer, co-founder of PGP Corporation, designer of OpenPGP, ZRTP, and SPKI contributor. Known for meticulous documentation and thoughtful API design.

---

*Added to the Library of Cyberspace, January 2026*
