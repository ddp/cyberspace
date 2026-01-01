# foof-loop - Extensible Looping Facility

**Source:** http://wiki.call-cc.org/eggref/5/foof-loop

## Overview

foof-loop is a Scheme looping facility providing extensible iteration patterns. It aims to "give names to these patterns by which they can be composed together in a unified LOOP macro."

## Core Concept

Rather than repeating loop structures for lists, vectors, and other sequences, foof-loop abstracts iteration patterns through named iterators like `IN-LIST`, `IN-VECTOR`, and `IN-PORT`.

## Basic Syntax

```scheme
(LOOP [<loop-name>] (<loop-clause> ...)
  [=> <final-expression>]
  [<body>])
```

**Components:**
- `loop-name` (optional) - For named continuation
- `loop-clause` - Variable bindings and iteration control
- `final-expression` (optional) - Value returned when loop terminates
- `body` (optional) - Code executed each iteration

## Loop Clauses

### WITH - Loop Variables

```scheme
(WITH var init [update])
```

Introduces loop variables with initializers and optional update expressions.

### FOR - Iterator Dispatch

```scheme
(FOR var (iterator args ...))
```

Dispatches to iterators, binding variables during iteration.

### LET/LET-VALUES - Body Bindings

```scheme
(LET ((var expr) ...))
(LET-VALUES (((var ...) expr) ...))
```

Binds expressions within loop body.

### WHILE/UNTIL - Conditional Termination

```scheme
(WHILE condition)
(UNTIL condition)
```

Conditional termination based on expressions.

## Key Iterators

### List Iteration

```scheme
(IN-LIST list)                           ; Step through list pairs
(IN-LISTS list ...)                      ; Parallel iteration
```

**Example:**

```scheme
(loop ((for x (in-list '(1 2 3 4))))
  (display x))
```

### Vector/String Iteration

```scheme
(IN-VECTOR vector [start end])           ; Forward iteration
(IN-VECTOR-REVERSE vector [start end])   ; Reverse iteration
(IN-STRING string [start end])           ; Forward string iteration
(IN-STRING-REVERSE string [start end])   ; Reverse string iteration
```

**Important:** Lower bounds are inclusive. Upper bounds are exclusive.

### Numeric Iteration

```scheme
(UP-FROM start [to limit] [by step])     ; Incremental
(DOWN-FROM start [to limit] [by step])   ; Decremental
```

**Example:**

```scheme
(loop ((for i (up-from 0 (to 10) (by 2))))
  (display i))
; Prints: 0 2 4 6 8
```

### Input Iteration

```scheme
(IN-PORT port [reader])                  ; Read successive data
(IN-FILE filename [reader])              ; Open, read, close automatically
```

**Example:**

```scheme
(loop ((for line (in-file "data.txt" read-line)))
  (process line))
```

## Accumulating Iterators

### List Accumulators

```scheme
(LISTING expr)                           ; Accumulate in order
(LISTING-REVERSE expr)                   ; Accumulate in reverse
(APPENDING expr)                         ; Concatenate lists
(LISTING! expr)                          ; In-place building (non-reentrant)
(LISTING-INTO! list expr)                ; Build into existing list
```

**Example:**

```scheme
(loop ((for x (in-list '(1 2 3)))
       (for squares (listing (* x x))))
  => squares)
; Returns: (1 4 9)
```

### Numerical Accumulators

```scheme
(SUMMING expr [init])                    ; Accumulate sums
(MULTIPLYING expr [init])                ; Accumulate products
(MINIMIZING expr [init])                 ; Find minimum
(MAXIMIZING expr [init])                 ; Find maximum
```

**Example:**

```scheme
(loop ((for x (in-list '(1 2 3 4 5)))
       (for total (summing x)))
  => total)
; Returns: 15
```

## Advanced Examples

### Filtering with Accumulation

```scheme
(loop ((for x (in-list '(1 2 3 4 5 6)))
       (for evens (listing (if (even? x) x))))
  => evens)
; Returns: (2 4 6)
```

### Parallel Iteration

```scheme
(loop ((for x (in-list '(1 2 3)))
       (for y (in-list '(a b c)))
       (for pairs (listing (cons x y))))
  => pairs)
; Returns: ((1 . a) (2 . b) (3 . c))
```

### Named Loop with Continuation

```scheme
(loop loop-name ((with i 0))
  (when (< i 10)
    (display i)
    (loop-name (+ i 1))))
```

### Complex Accumulation

```scheme
(loop ((for line (in-file "numbers.txt" read-line))
       (for num (in-list (map string->number (string-split line))))
       (for sum (summing num))
       (for count (summing 1)))
  => (/ sum count))
; Computes average
```

## Variable Classes

The system uses different variable classes with distinct scoping rules:

1. **Loop variables** - Persist across iterations (WITH)
2. **Entry variables** - Computed at loop entry
3. **Body variables** - Bound in loop body (LET)
4. **User variables** - Accumulators
5. **Final variables** - Available only in final expression

## Custom Iterator Development

Custom iterators use continuation-passing style, invoking a continuation with specifications for:
- Outer bindings
- Loop variables
- Entry bindings
- Termination conditions
- Body bindings
- Final bindings

Error reporting uses `SYNTACTIC-ERROR` and `LOOP-CLAUSE-ERROR` for user-friendly messages.

## Efficiency Considerations

foof-loop generates code using:
- Rebinding rather than assignment
- LET-VALUES for multiple return values
- Generic arithmetic (optimization delegated to compiler)

## Important Notes

1. **Non-reentrant iterators** (marked with `!`) use destructive operations and cannot safely support recursive re-entry
2. **Bounds convention:** Lower bounds are inclusive, upper bounds are exclusive (applies consistently)
3. **Loop continuation** can be explicit (named loop) or implicit (unnamed loop)

## Installation

```bash
chicken-install foof-loop
```

## See Also

- loop (simple loop egg)
- SRFI-42 (eager comprehensions)
- Common Lisp LOOP macro (inspiration)
