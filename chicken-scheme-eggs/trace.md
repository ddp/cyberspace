# trace - Procedure Tracing and Breakpoints

**Source:** http://wiki.call-cc.org/eggref/5/trace

**License:** Public domain

**Dependencies:** advice, miscmacros

## Overview

The trace egg provides "traced execution of procedures and setting breakpoints on procedure entry" for CHICKEN Scheme, replacing tracing facilities from versions prior to 4.2.12.

## Core Procedures

### `trace`

```scheme
(trace PROCEDURE ...)
(trace)  ; Lists currently traced procedures
```

Modifies procedures to print entry/exit information.

**Example:**

```scheme
(import trace)

(define (factorial n)
  (if (<= n 1)
      1
      (* n (factorial (- n 1)))))

(trace factorial)

(factorial 5)
; Prints:
; |(factorial 5)
; | (factorial 4)
; | |(factorial 3)
; | | (factorial 2)
; | | |(factorial 1)
; | | |factorial => 1
; | | factorial => 2
; | |factorial => 6
; | factorial => 24
; |factorial => 120
; => 120
```

### `untrace`

```scheme
(untrace PROCEDURE ...)
(untrace)  ; Untraces all procedures
```

Removes tracing from specified procedures.

**Example:**

```scheme
(untrace factorial)
```

### `trace/untrace`

```scheme
(trace/untrace PROCEDURE ...)
```

Toggles tracing on/off for given procedures.

**Example:**

```scheme
(trace/untrace factorial)  ; If traced, untrace; if not traced, trace
```

### `trace-module`

```scheme
(trace-module MODULE-NAME ...)
```

Traces all exported toplevel procedures from specified module names.

**Note:** Core library modules cannot be traced.

**Example:**

```scheme
(trace-module my-utilities)
```

### `untrace-module`

```scheme
(untrace-module MODULE-NAME ...)
```

Removes tracing from currently traced exports of given modules.

## Breakpoints

### `break`

```scheme
(break PROCEDURE ...)
(break)  ; Lists active breakpoints
```

Sets breakpoints on procedures, signaling a condition on entry.

**Example:**

```scheme
(break factorial)

(factorial 3)
; Breaks at factorial entry with debugger prompt
```

### `unbreak`

```scheme
(unbreak PROCEDURE ...)
(unbreak)  ; Removes all breakpoints
```

Removes breakpoints from specified procedures.

### `continue` (alias: `c`)

```scheme
(continue [CONDITION])
```

Resumes execution from a breakpoint.

**Example:**

```scheme
#;> (break factorial)
#;> (factorial 3)
; [breakpoint in factorial]
#;> (continue)
; Continues execution
```

## Configuration Parameters

### `trace-output-port`

```scheme
(trace-output-port [PORT])
```

Directs tracing output; defaults to current output port.

**Example:**

```scheme
(trace-output-port (current-error-port))  ; Trace to stderr
```

### `trace-verbose`

```scheme
(trace-verbose [BOOLEAN])
```

Controls informational messages when enabling/disabling tracing.

**Default:** `#t`

**Example:**

```scheme
(trace-verbose #f)  ; Suppress "tracing procedure..." messages
```

### `trace-length-limit`

```scheme
(trace-length-limit [N])
```

Sets maximum character length for traced procedure plus arguments display.

**Default:** `#f` (unlimited)

**Example:**

```scheme
(trace-length-limit 80)  ; Truncate display to 80 characters
```

### `trace-call-sites`

```scheme
(trace-call-sites [BOOLEAN])
```

When enabled, displays call site information from trace buffer.

**Requirement:** Code must be compiled with `-d2` or higher debugging level.

**Default:** `#f`

**Example:**

```scheme
(trace-call-sites #t)
```

### `trace-call-site-length-limit`

```scheme
(trace-call-site-length-limit [N])
```

Limits call site text to specified character length.

**Default:** `100`

**Example:**

```scheme
(trace-call-site-length-limit 50)
```

## Advanced Examples

### Tracing Multiple Procedures

```scheme
(define (add a b) (+ a b))
(define (multiply a b) (* a b))
(define (square x) (multiply x x))

(trace add multiply square)

(square 5)
; |(square 5)
; | (multiply 5 5)
; | |(add 5 0)
; | |add => 5
; | multiply => 25
; |square => 25
```

### Tracing with Output Control

```scheme
(trace-length-limit 40)
(trace-verbose #f)

(define (long-args x y z w)
  (list x y z w))

(trace long-args)
(long-args "very-long-string-argument"
           "another-long-string"
           "and-another"
           "final-argument")
; Display will be truncated at 40 chars
```

### Debugging with Breakpoints

```scheme
(define (buggy-function x)
  (let ((result (* x 2)))
    (if (> result 10)
        (error "Result too large!")
        result)))

(break buggy-function)

(buggy-function 3)
; Breakpoint hit - can inspect state
#;> (continue)
; => 6

(buggy-function 6)
; Breakpoint hit
#;> (continue)
; Error: Result too large!
```

### Module-Level Tracing

```scheme
(module math-utils (add-three multiply-two)
  (import scheme chicken.base)

  (define (add-three x) (+ x 3))
  (define (multiply-two x) (* x 2)))

(import math-utils)
(trace-module math-utils)

(add-three 5)
; |(add-three 5)
; |add-three => 8
```

### Call Site Information

```scheme
;; Compile with: csc -d2 myfile.scm

(trace-call-sites #t)
(trace-call-site-length-limit 60)

(define (helper x) (* x 2))
(define (main) (helper 42))

(trace helper)
(main)
; Shows file:line information where helper was called
```

## Combining Trace with REPL

The trace egg works well in the REPL for interactive debugging:

```scheme
#;> (import trace)
#;> (define (fib n)
      (if (< n 2)
          n
          (+ (fib (- n 1)) (fib (- n 2)))))
#;> (trace fib)
#;> (fib 4)
; Shows complete call tree
```

## Installation

```bash
chicken-install trace
```

## See Also

- advice (underlying advice mechanism)
- debug (debugging utilities)
- chicken-doc (documentation lookup)
