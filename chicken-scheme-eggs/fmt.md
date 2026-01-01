# fmt - Combinatory Formatting

**Source:** http://wiki.call-cc.org/eggref/5/fmt

## Overview

The **fmt** library is a CHICKEN Scheme package for flexible text formatting. It provides procedures for formatting Scheme objects to text in various ways without requiring intermediate string capture.

## Core Philosophy

Rather than template-based formatting, fmt uses combinators—nested closures that generate output on-demand. This approach prioritizes:
1. **Expressiveness/extensibility** (primary goal)
2. **Scalability** - No unnecessary intermediate data
3. **Brevity** - Concise combinator syntax

## Primary Interface

```scheme
(fmt <output-dest> <format> ...)
```

**Output destinations:**
- Output port - Direct port output
- `#t` - Current output port
- `#f` - Accumulate and return as string

## Basic Formatting

### Display and Write

```scheme
(dsp obj)        ; Display semantics (strings unquoted)
(wrt obj)        ; Write semantics with shared structure handling
(pretty obj)     ; Pretty-printing with tabular vector formatting
```

### String Escaping

```scheme
(slashified str)           ; Always quote/escape
(maybe-slashified str)     ; Quote/escape only if needed
```

## Number Formatting

```scheme
(num n [radix precision sign-rule comma-rule comma-sep decimal-sep])
(num/comma n)              ; Comma-separated thousands
(num/si n [base])          ; SI unit abbreviations (Ki, Mi, Gi)
(num/roman n)              ; Roman numeral conversion
```

**Example:**

```scheme
(fmt #f (num 1234567.89))           ; "1234567.89"
(fmt #f (num/comma 1234567.89))     ; "1,234,567.89"
(fmt #f (num/si 1024))              ; "1Ki"
```

## Spacing and Alignment

### Line Control

```scheme
nl               ; Newline constant
fl               ; Fresh-line (newline only if not at start of line)
(space-to col)   ; Advance to column
(tab-to col)     ; Tab to column
```

### Padding and Trimming

```scheme
(pad width fmt)              ; Pad to width (right-aligned)
(pad/left width fmt)         ; Pad to width (left-aligned)
(pad/both width fmt)         ; Center in width

(trim width fmt)             ; Truncate to width
(trim/left width fmt)        ; Truncate from left
(trim/both width fmt)        ; Truncate from both sides

(fit width fmt)              ; Combined padding/trimming
```

**Example:**

```scheme
(fmt #f (pad 10 "hello"))           ; "     hello"
(fmt #f (pad/left 10 "hello"))      ; "hello     "
(fmt #f (pad/both 10 "hi"))         ; "    hi    "
```

## Concatenation and Joining

```scheme
(cat fmt ...)                ; Simple concatenation
(fmt-join fmt-list [sep])    ; Join with separator
(fmt-join/prefix fmt-list [prefix])
(fmt-join/suffix fmt-list [suffix])
(fmt-join/last fmt-list sep last-sep)
(fmt-join/dot fmt-list sep dot-sep)
```

**Example:**

```scheme
(fmt #f (fmt-join '("a" "b" "c") ", "))    ; "a, b, c"
(fmt #f (fmt-join/last '("a" "b" "c") ", " " and "))  ; "a, b and c"
```

## Format Variables

```scheme
(fmt-let ((var value) ...) fmt ...)     ; Scoped state modification
(fmt-bind var fmt ...)                   ; Bind format variable

;; Common variables:
radix              ; Numeric base (default 10)
fix                ; Decimal precision
decimal-align      ; Decimal point alignment for tables
pad-char           ; Padding character (default space)
ellipse            ; Truncation indicator (default "...")
```

**Example:**

```scheme
(fmt #f (fmt-let ((radix 16)) (num 255)))           ; "ff"
(fmt #f (fmt-let ((fix 2)) (num 3.14159)))          ; "3.14"
```

## Columnar Formatting

```scheme
(columnar col-widths fmt-list)          ; Side-by-side columns
(tabular fmt-list)                       ; Auto-width columns
(wrap-lines width fmt)                   ; Text wrapping
(justify width fmt)                      ; Full justification
(fmt-file filename)                      ; Stream file display
```

## C Code Generation

### Control Flow

```scheme
(c-if test then else)
(c-for init test update body)
(c-while test body)
(c-switch expr (c-case val body) ...)
```

### Declarations

```scheme
(c-fun return-type name params body)
(c-prototype return-type name params)
(c-var type name [init])
(c-struct name fields)
(c-enum name values)
```

### Operators

All C operators available with `c-` prefix:

```scheme
(c+ a b)           ; Addition
(c-or a b)         ; Logical OR
(c-== a b)         ; Equality
(c-&& a b)         ; Logical AND
```

### Preprocessor

```scheme
(cpp-include file)
(cpp-define name value)
(cpp-ifdef name then else)
(cpp-pragma directive)
```

### Style Customization

```scheme
(fmt-let (('indent-space 2)
          ('newline-before-brace? #f)    ; K&R vs. non-K&R
          ('non-spaced-ops? #t))         ; Compact operators
  (c-fun "int" "factorial" '("int n")
    ...))
```

### S-expression to C Conversion

```scheme
(c-expr '(%fun factorial (%var n)))
```

Special keywords:
- `%fun` - Function call
- `%var` - Variable reference
- `%array` - Array access

## Advanced Features

### Color Output (fmt-color egg)

```scheme
(fmt-red text)
(fmt-blue text)
(fmt-green text)
```

Supports ANSI escape sequences or HTML span tags.

### Unicode Support (fmt-unicode egg)

- Proper width calculation for double-width characters
- Combining character handling

## State Management

Formatters operate within a format state tracking:
- Current row and column
- User-defined variables
- Context for features like automatic return insertion in C functions

## Example: Complete Usage

```scheme
(import fmt)

;; Simple string formatting
(fmt #f "Hello " (dsp "World") "!")  ; "Hello World!"

;; Number formatting with alignment
(fmt #f
  (columnar 2
    (list (num 123.45)
          (num 6789.01))))

;; C code generation
(fmt #f
  (c-fun "int" "add" '("int a" "int b")
    (c-return (c+ (c-var "a") (c-var "b")))))
```

## Installation

```bash
chicken-install fmt
```

## See Also

- format (template-based formatting)
- printf (traditional printf-style)
- pretty-print (CHICKEN core)
