# loop - Common Lisp Loop Macro

**Source:** http://wiki.call-cc.org/eggref/5/loop

**License:** GNU General Public License v2 or later

**Author:** Heinrich Taube

**Maintainer:** Ported by Felix Winkelmann (CHICKEN 4), Massimo Nocentini (CHICKEN 5)

**Dependencies:** srfi-1

## Overview

The loop egg is "A Scheme version of the Common Lisp loop macro." It provides a powerful iteration construct with declarative syntax for common looping patterns.

## Core Syntax

```scheme
(loop CLAUSE ...)
```

Executes forms repeatedly across multiple clauses. The implementation draws from CLtL2 (Common Lisp the Language, 2nd Edition) specifications.

## Basic Example

```scheme
(import loop)

(loop with a = 0 and b = -1
      while (< a 10)
      sum a into foo
      do (set! a (+ a 1))
      finally (return (list foo b)))
;=> (45 -1)
```

## Common Clauses

### Variable Initialization

```scheme
with VAR = EXPR [and VAR = EXPR ...]
```

Initialize loop variables.

### Iteration

```scheme
for VAR from START to END [by STEP]
for VAR in LIST
for VAR = EXPR [then UPDATE-EXPR]
```

**Examples:**

```scheme
(loop for i from 1 to 5
      collect i)
;=> (1 2 3 4 5)

(loop for x in '(a b c d)
      collect x)
;=> (a b c d)

(loop for i from 0 to 10 by 2
      collect i)
;=> (0 2 4 6 8 10)
```

### Conditionals

```scheme
while CONDITION
until CONDITION
when CONDITION
unless CONDITION
```

**Examples:**

```scheme
(loop for i from 1
      while (< i 5)
      collect i)
;=> (1 2 3 4)

(loop for i in '(1 2 3 4 5)
      when (even? i)
      collect i)
;=> (2 4)
```

### Accumulation

```scheme
collect EXPR [into VAR]
append EXPR [into VAR]
sum EXPR [into VAR]
count EXPR [into VAR]
maximize EXPR [into VAR]
minimize EXPR [into VAR]
```

**Examples:**

```scheme
(loop for i from 1 to 5
      collect (* i i))
;=> (1 4 9 16 25)

(loop for i in '(1 2 3 4 5)
      sum i)
;=> 15

(loop for i in '(3 7 2 9 4)
      maximize i)
;=> 9

(loop for i from 1 to 10
      count (even? i))
;=> 5
```

### Actions

```scheme
do EXPR ...
```

Execute arbitrary expressions in the loop body.

```scheme
(loop for i from 1 to 3
      do (display i)
         (newline))
; Prints:
; 1
; 2
; 3
```

### Termination

```scheme
finally (return EXPR)
```

Return a value when the loop completes.

```scheme
(loop for i from 1 to 5
      sum i into total
      finally (return total))
;=> 15
```

## Advanced Examples

### Multiple Accumulators

```scheme
(loop for i from 1 to 10
      when (even? i)
        sum i into even-sum
      else
        sum i into odd-sum
      finally (return (list even-sum odd-sum)))
;=> (30 25)
```

### Nested Iteration

```scheme
(loop for x in '(1 2 3)
      append (loop for y in '(a b)
                   collect (cons x y)))
;=> ((1 . a) (1 . b) (2 . a) (2 . b) (3 . a) (3 . b))
```

### List Processing

```scheme
(loop for item in '(1 2 3 4 5 6)
      for squared = (* item item)
      when (> squared 10)
      collect squared)
;=> (16 25 36)
```

### Finding Elements

```scheme
(loop for x in '(1 3 5 8 9 10)
      when (even? x)
      return x)
;=> 8
```

### Parallel Iteration

```scheme
(loop for x in '(1 2 3)
      for y in '(a b c)
      collect (cons x y))
;=> ((1 . a) (2 . b) (3 . c))
```

### With Initialization and Multiple Actions

```scheme
(loop with max = 0
      for i in '(3 7 2 9 4)
      when (> i max)
        do (set! max i)
      finally (return max))
;=> 9
```

## Comparison with foof-loop

While both provide iteration facilities:
- **loop** follows Common Lisp conventions with keyword-based syntax
- **foof-loop** uses more Scheme-like syntax with parenthesized iterators

Choose loop for:
- Familiarity with Common Lisp
- Complex accumulation patterns
- Declarative iteration style

Choose foof-loop for:
- More Scheme-like syntax
- Custom iterator extensions
- Functional programming style

## Version History

- **1.5** - Ported to CHICKEN 5 (Massimo Nocentini)
- **1.1** - Ported to CHICKEN 4 (Felix Winkelmann)
- **1.0** - Initial release

## Installation

```bash
chicken-install loop
```

## See Also

- Common Lisp HyperSpec (LOOP macro documentation)
- foof-loop (alternative looping facility)
- SRFI-42 (eager comprehensions)
