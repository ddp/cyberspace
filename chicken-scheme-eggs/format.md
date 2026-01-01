# format - Common Lisp Style Formatting

**Source:** http://wiki.call-cc.org/eggref/5/format

**License:** Public domain

**Author:** Dirk Lutzebaeck (original SLIB version)

**Dependencies:** None

## Overview

The format egg provides "an almost complete implementation of Common LISP format description according to the CL reference book **Common LISP, the Language**." Originally derived from SLIB, it implements SRFI-28.

## Core Procedure

```scheme
(format DESTINATION FORMAT-STRING . ARGUMENTS)
```

Handles formatted output with flexible destination handling:

**Destination options:**
- `#t` - Outputs to current port, returns `#t`
- `#f` - Returns formatted string
- String - Treats it as format string, returns result
- Number - Outputs to error port
- Output port - Writes to that port, returns `#t`

## Basic Usage

```scheme
(format #f "Hello ~A!" "World")           ; => "Hello World!"
(format #t "Number: ~D~%" 42)             ; Prints to stdout
(format #f "~S" '(a b c))                 ; => "(a b c)"
```

## Supported Directives

### Basic Output

- `~A` - Any (aesthetic output, like display)
- `~S` - S-expression (like write)
- `~D` - Decimal integer
- `~C` - Character

### Number Bases

- `~X` - Hexadecimal
- `~O` - Octal
- `~B` - Binary
- `~R` - Radix (general base)

**Examples:**

```scheme
(format #f "~X" 255)                      ; => "FF"
(format #f "~O" 64)                       ; => "100"
(format #f "~B" 7)                        ; => "111"
(format #f "~R" 42)                       ; => "forty-two"
```

### Floating-Point

- `~F` - Fixed-format floating-point
- `~E` - Exponential format
- `~G` - General floating-point
- `~$` - Monetary (dollars)

**Examples:**

```scheme
(format #f "~F" 3.14159)                  ; => "3.14159"
(format #f "~,2F" 3.14159)                ; => "3.14"
(format #f "~E" 1234.5)                   ; => "1.2345E+3"
(format #f "~$" 12.3)                     ; => "12.30"
```

### Text Control

- `~%` - Newline
- `~|` - Page separator
- `~T` - Tab to column
- `~(...)~` - Case conversion
  - `~(...~)` - Downcase
  - `~:(...~)` - Upcase first letter
  - `~@(...~)` - Upcase first letter of each word
  - `~:@(...~)` - Upcase all

**Examples:**

```scheme
(format #f "Line 1~%Line 2")              ; Two lines
(format #f "~(HELLO~)")                   ; => "hello"
(format #f "~:(hello world~)")            ; => "Hello world"
(format #f "~@:(hello world~)")           ; => "Hello World"
```

### Flow Control

#### Conditional - `~[...~]`

```scheme
(format #f "~[zero~;one~;two~]" 1)        ; => "one"
(format #f "~:[false~;true~]" #t)         ; => "true"
```

#### Iteration - `~{...~}`

```scheme
(format #f "~{~A~^, ~}" '(a b c))         ; => "a, b, c"
```

#### Argument Jumping - `~*`

- `~*` - Skip forward one argument
- `~:*` - Skip backward one argument
- `~n*` - Skip forward n arguments

### Special Control

- `~^` - Up and out (escape from iteration/conditional)
- `~?` - Indirection (recursive format)
- `~!` - Flush output

## Directive Parameters

Many directives accept parameters:

```scheme
~minCOL,colINC,minPAD,padCHAR@:T      ; Tab parameters
~width,padCHARA                        ; Aesthetic with padding
~radix,minDIGR                         ; Radix with minimum digits
```

**Examples:**

```scheme
(format #f "~10A" "hi")                   ; => "hi        "
(format #f "~10@A" "hi")                  ; => "        hi"
(format #f "~5,'0D" 42)                   ; => "00042"
```

## Configuration Variables

```scheme
format:max-iterations                     ; Default: 100
format:fn-max                            ; Default: 200 digits
format:complex-numbers                   ; Default: #f
format:unprocessed-arguments-error?      ; Default: #f
```

**Example:**

```scheme
(set! format:max-iterations 1000)
```

## Complete Example

```scheme
(import format)

;; Report generation
(define (print-report name age balance)
  (format #t "~%Customer Report~%")
  (format #t "~15A: ~A~%" "Name" name)
  (format #t "~15A: ~D years~%" "Age" age)
  (format #t "~15A: ~$~%" "Balance" balance))

(print-report "Alice" 30 1234.56)
; Prints:
; Customer Report
; Name           : Alice
; Age            : 30 years
; Balance        : 1234.56
```

## Important Limitations

**Thread Safety:** "This code is not reentrant, nor is it thread-safe."

Do not use format concurrently from multiple threads without external synchronization.

## Installation

```bash
chicken-install format
```

## See Also

- SRFI-28 (basic format)
- fmt (combinator-based formatting)
- printf (C-style formatting)
- Common Lisp HyperSpec (full directive documentation)
