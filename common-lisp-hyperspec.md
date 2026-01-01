# Common Lisp HyperSpec - Reference Guide

**Source:** http://www.lispworks.com/documentation/HyperSpec/

**Curator:** Kent Pitman (X3J13 Project Editor)

**Maintained by:** LispWorks Ltd.

**Copyright:** 1996-2005 LispWorks Ltd.

## Overview

The Common Lisp HyperSpec (CLHS) is an HTML version of the ANSI Common Lisp standard (ANSI X3.226). It is the authoritative reference for Common Lisp programming and is freely available online.

## Main Entry Points

**Primary Navigation:**
- **Front Page:** http://www.lispworks.com/documentation/HyperSpec/Front/index.htm
- **Table of Contents:** http://www.lispworks.com/documentation/HyperSpec/Front/Contents.htm
- **Master Index:** http://www.lispworks.com/documentation/HyperSpec/Front/X_Master.htm
- **Symbol Index:** http://www.lispworks.com/documentation/HyperSpec/Front/X_Symbol.htm
- **Glossary:** http://www.lispworks.com/documentation/HyperSpec/Body/26_glo.htm
- **Permuted Symbol Index:** http://www.lispworks.com/documentation/HyperSpec/Front/X_Perm_Sym.htm

## Chapter Organization

### Chapter 1: Introduction
http://www.lispworks.com/documentation/HyperSpec/Body/01_.htm

Covers:
- Scope, purpose, and history of Common Lisp
- Document organization
- Referenced publications
- Definitions and terminology
- Conformance requirements
- Language extensions and subsets
- Deprecated features
- Symbols in the COMMON-LISP package

### Chapter 2: Syntax
http://www.lispworks.com/documentation/HyperSpec/Body/02_.htm

Covers:
- Character syntax
- Reader algorithm
- Standard characters
- Macro characters
- Tokens and parsing
- Backquote notation
- Sharpsign dispatching

### Chapter 3: Evaluation and Compilation
http://www.lispworks.com/documentation/HyperSpec/Body/03_.htm

Covers:
- Form evaluation
- Special forms
- Lambda expressions
- Closures
- Compilation model
- Minimal compilation
- Compiler macros

### Chapter 4: Types and Classes
http://www.lispworks.com/documentation/HyperSpec/Body/04_.htm

Covers:
- Type system overview
- Type specifiers
- Type relationships
- Class hierarchy
- Defining types and classes
- Type declarations

### Chapter 5: Data and Control Flow
http://www.lispworks.com/documentation/HyperSpec/Body/05_.htm

Covers:
- Generalized reference (setf, setq)
- Transfer of control (block, return, tagbody, go)
- Conditionals (if, cond, case, when, unless)
- Logical operators (and, or, not)
- Mapping functions (mapcar, mapcan, etc.)
- Variables and constants
- Assignment operators

**Key functions:** let, let*, setf, progn, prog1, prog2, apply, funcall, values, multiple-value-bind

### Chapter 6: Iteration
http://www.lispworks.com/documentation/HyperSpec/Body/06_.htm

Covers:
- loop macro (comprehensive iteration facility)
- do, do*, dotimes, dolist
- Mapping across sequences

### Chapter 7: Objects (CLOS)
http://www.lispworks.com/documentation/HyperSpec/Body/07_.htm

Covers:
- Object creation and initialization
- Changing the class of an instance
- Reinitializing instances
- Meta-objects and MOP
- Slots and slot access
- Generic functions and methods
- Method combination

**Key macros:** defclass, defgeneric, defmethod, make-instance, with-slots, slot-value

### Chapter 8: Structures
http://www.lispworks.com/documentation/HyperSpec/Body/08_.htm

Covers:
- defstruct macro
- Structure slot options
- Structure constructors
- Structure accessors
- Inheritance

### Chapter 9: Conditions
http://www.lispworks.com/documentation/HyperSpec/Body/09_.htm

Covers:
- Condition system
- Error handling
- Restarts
- Signaling conditions
- Defining conditions

**Key macros:** handler-case, handler-bind, ignore-errors, define-condition, signal, error, warn

### Chapter 10: Symbols
http://www.lispworks.com/documentation/HyperSpec/Body/10_.htm

Covers:
- Symbol components (name, value, function, plist)
- Symbol creation
- Symbol properties
- Keywords

**Key functions:** symbol-name, symbol-value, symbol-function, symbol-plist, gensym, gentemp

### Chapter 11: Packages
http://www.lispworks.com/documentation/HyperSpec/Body/11_.htm

Covers:
- Package system
- Package operations
- Symbol import/export
- Package inheritance
- Name conflicts

**Key functions:** defpackage, in-package, use-package, import, export, find-symbol, intern

### Chapter 12: Numbers
http://www.lispworks.com/documentation/HyperSpec/Body/12_.htm

Covers:
- Numeric tower
- Arithmetic operations
- Comparison operators
- Mathematical functions
- Random numbers
- Complex numbers
- Rational numbers

**Key functions:** +, -, *, /, =, <, >, min, max, abs, sqrt, expt, sin, cos, random

### Chapter 13: Characters
http://www.lispworks.com/documentation/HyperSpec/Body/13_.htm

Covers:
- Character types
- Character comparisons
- Character attributes
- Case conversion

**Key functions:** char=, char<, char-upcase, char-downcase, digit-char-p, alpha-char-p

### Chapter 14: Conses (Lists)
http://www.lispworks.com/documentation/HyperSpec/Body/14_.htm

Covers:
- Cons cells
- List operations
- Association lists
- Property lists
- Trees

**Key functions:** cons, car, cdr, list, append, reverse, member, assoc, mapcar, reduce

### Chapter 15: Arrays
http://www.lispworks.com/documentation/HyperSpec/Body/15_.htm

Covers:
- Array creation
- Array access
- Specialized arrays
- Multi-dimensional arrays
- Adjustable arrays

**Key functions:** make-array, aref, array-dimension, array-rank, adjust-array

### Chapter 16: Strings
http://www.lispworks.com/documentation/HyperSpec/Body/16_.htm

Covers:
- String creation
- String comparison
- String manipulation
- Case conversion

**Key functions:** string, string=, string<, string-upcase, string-downcase, string-trim

### Chapter 17: Sequences
http://www.lispworks.com/documentation/HyperSpec/Body/17_.htm

Covers:
- Generic sequence operations
- Sequence predicates
- Sorting and merging
- Sequence transformations

**Key functions:** length, elt, subseq, concatenate, position, find, count, remove, substitute, sort

### Chapter 18: Hash Tables
http://www.lispworks.com/documentation/HyperSpec/Body/18_.htm

Covers:
- Hash table creation
- Hash table access
- Hash table iteration
- Hash table tests

**Key functions:** make-hash-table, gethash, remhash, maphash, hash-table-count

### Chapter 19: Filenames (Pathnames)
http://www.lispworks.com/documentation/HyperSpec/Body/19_.htm

Covers:
- Pathname components
- Pathname operations
- Logical pathnames
- Namestrings

**Key functions:** pathname, make-pathname, pathname-name, pathname-type, merge-pathnames

### Chapter 20: Files
http://www.lispworks.com/documentation/HyperSpec/Body/20_.htm

Covers:
- File operations
- Directory operations
- File attributes
- File deletion and renaming

**Key functions:** open, close, with-open-file, delete-file, rename-file, directory

### Chapter 21: Streams
http://www.lispworks.com/documentation/HyperSpec/Body/21_.htm

Covers:
- Stream types
- Stream operations
- Input/output functions
- String streams
- File streams

**Key functions:** read, write, print, format, read-line, read-char, write-char, make-string-input-stream

### Chapter 22: Printer
http://www.lispworks.com/documentation/HyperSpec/Body/22_.htm

Covers:
- Printer control
- Pretty printing
- Format directives
- Print representations

**Key functions:** print, prin1, princ, pprint, format, write, write-to-string

**Format directive reference:** Comprehensive guide to ~-directives

### Chapter 23: Reader
http://www.lispworks.com/documentation/HyperSpec/Body/23_.htm

Covers:
- Reader algorithm
- Reader macros
- Readtable manipulation
- Sharpsign syntax

**Key functions:** read, read-from-string, readtable-case, set-macro-character, set-dispatch-macro-character

### Chapter 24: System Construction
http://www.lispworks.com/documentation/HyperSpec/Body/24_.htm

Covers:
- compile, compile-file
- load
- provide, require
- Module system

### Chapter 25: Environment
http://www.lispworks.com/documentation/HyperSpec/Body/25_.htm

Covers:
- Time functions
- Debugging utilities
- Environment queries
- Program termination

**Key functions:** time, trace, untrace, step, describe, inspect, room, lisp-implementation-type

### Chapter 26: Glossary
http://www.lispworks.com/documentation/HyperSpec/Body/26_glo.htm

Comprehensive terminology definitions for Common Lisp concepts.

## Quick Reference Links

### Commonly Referenced Symbols

**Core Macros:**
- `defun`: http://www.lispworks.com/documentation/HyperSpec/Body/m_defun.htm
- `defmacro`: http://www.lispworks.com/documentation/HyperSpec/Body/m_defmac.htm
- `defvar`: http://www.lispworks.com/documentation/HyperSpec/Body/m_defv_d.htm
- `defparameter`: http://www.lispworks.com/documentation/HyperSpec/Body/m_defpar.htm
- `let`: http://www.lispworks.com/documentation/HyperSpec/Body/s_let_l.htm
- `lambda`: http://www.lispworks.com/documentation/HyperSpec/Body/m_lambda.htm

**CLOS:**
- `defclass`: http://www.lispworks.com/documentation/HyperSpec/Body/m_defcla.htm
- `defgeneric`: http://www.lispworks.com/documentation/HyperSpec/Body/m_defgen.htm
- `defmethod`: http://www.lispworks.com/documentation/HyperSpec/Body/m_defmet.htm

**Loop:**
- `loop`: http://www.lispworks.com/documentation/HyperSpec/Body/m_loop.htm

**Conditions:**
- `handler-case`: http://www.lispworks.com/documentation/HyperSpec/Body/m_hand_1.htm
- `handler-bind`: http://www.lispworks.com/documentation/HyperSpec/Body/m_hand_1.htm
- `error`: http://www.lispworks.com/documentation/HyperSpec/Body/f_error.htm

**Format:**
- `format`: http://www.lispworks.com/documentation/HyperSpec/Body/f_format.htm

## URL Structure

The HyperSpec uses a consistent URL pattern for quick access:

**Functions:** `http://www.lispworks.com/documentation/HyperSpec/Body/f_SYMBOL.htm`

**Macros:** `http://www.lispworks.com/documentation/HyperSpec/Body/m_SYMBOL.htm`

**Special Operators:** `http://www.lispworks.com/documentation/HyperSpec/Body/s_SYMBOL.htm`

**Types:** `http://www.lispworks.com/documentation/HyperSpec/Body/t_SYMBOL.htm`

**Variables:** `http://www.lispworks.com/documentation/HyperSpec/Body/v_SYMBOL.htm`

Where SYMBOL is the (abbreviated) symbol name with special characters replaced.

## Offline Access

The HyperSpec can be downloaded for offline use. Several implementations provide local copies:

- Download from LispWorks: http://www.lispworks.com/documentation/common-lisp.html
- Many Common Lisp implementations include it in their documentation

## Integration with Development Tools

### Emacs/SLIME

Add to your `.emacs` to access HyperSpec directly:

```elisp
(require 'hyperspec)
(setq common-lisp-hyperspec-root
      "http://www.lispworks.com/documentation/HyperSpec/")

;; Look up symbol at point with C-c C-d h
```

### Command Line Lookup

Create a shell function:

```bash
clhs() {
    open "http://www.lispworks.com/documentation/HyperSpec/Front/X_AllSym.htm"
}
```

## Complementary Resources

**Books:**
- **Practical Common Lisp** by Peter Seibel - http://www.gigamonkeys.com/book/
- **Common Lisp: A Gentle Introduction** by David Touretzky
- **ANSI Common Lisp** by Paul Graham
- **On Lisp** by Paul Graham - http://www.paulgraham.com/onlisp.html

**Online Resources:**
- **Common Lisp Cookbook** - https://lispcookbook.github.io/cl-cookbook/
- **Awesome Common Lisp** - https://github.com/CodyReichert/awesome-cl
- **CLiki** - https://www.cliki.net/

**Community:**
- **Common Lisp Reddit** - https://www.reddit.com/r/Common_Lisp/
- **#commonlisp on Libera.Chat IRC**
- **Common Lisp Discord**

## Notes on the Standard

- The HyperSpec is based on ANSI X3.226, approved in 1994
- It is a faithful HTML rendering of the standard
- Kent Pitman was the editor of the X3J13 committee
- The document includes X3J13 issue documentation showing design decisions

## Using This Reference

When programming in Common Lisp:

1. **Start with the Symbol Index** for quick function/macro lookup
2. **Use the Permuted Index** to find functions by what they do
3. **Read relevant chapters** for understanding language features
4. **Check the Glossary** for precise terminology definitions
5. **Review X3J13 Issues** for rationale behind design decisions

## Legal Note

The Common Lisp HyperSpec is copyrighted by LispWorks Ltd. It is freely available for online access but redistribution requires permission. Always link to the canonical version at lispworks.com.

## Local Setup Recommendation

For best offline access:

```bash
# Download the HyperSpec
cd ~/docs
wget -r -np -nH --cut-dirs=2 http://www.lispworks.com/documentation/HyperSpec/

# Or use an implementation that bundles it
# SBCL, CCL, and others include it in their documentation
```

## Quick Tips

**Finding a function:**
- Know the name? Use Symbol Index
- Know what it does? Use Permuted Symbol Index or full Index
- Know the topic? Browse chapter contents

**Understanding errors:**
- Chapter 9 (Conditions) explains the condition system
- Chapter 25 (Environment) covers debugging utilities

**Learning advanced features:**
- Chapter 7 for CLOS
- Chapter 3 for macros and compilation
- Chapter 22 for format directives
- Chapter 6 for the loop macro

## See Also

- SBCL Manual (implementation-specific features)
- Chicken Scheme eggs (for Scheme comparison)
- **format** egg documentation (Scheme implementation of CL format)
- **loop** egg documentation (Scheme implementation of CL loop)
