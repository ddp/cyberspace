# dollar - Convenient Foreign Function Interface

**Source:** http://wiki.call-cc.org/eggref/5/dollar

**Authors:** Felix Winkelmann, Kon Lovett

**Version:** 3.0.0 (CHICKEN 5)

## Overview

The dollar egg is a CHICKEN Scheme library providing a convenience macro for direct invocation of foreign C/C++ functions.

## Core Syntax

### `$` Macro

```scheme
($ [RETURNTYPE] NAME (TYPE ARGUMENT) ...)
```

This macro enables calling C/C++ functions by:
1. Evaluating all arguments
2. Converting them to appropriate foreign types
3. Invoking the named function (must be a symbol)
4. Converting and returning results if a return type is specified (otherwise void)

## Type Handling

The macro accepts flexible argument forms:
- Evaluated Scheme expressions
- Literal data wrapped in `(quote LITERAL)`
- Pointers via `(location ...)`

Supported conversions include:
- Booleans
- Characters
- Numbers
- Strings
- SRFI-4 number vectors
- Symbols
- Other data passes as scheme-object type

## Usage

```scheme
(import dollar)
```

## Examples

### Basic printf Call

```scheme
($ printf "%d times Hello, %s!\n" 1000 "world")
; Prints: 1000 times Hello, world!
```

### Using Location and Return Type

```scheme
(define f 99.2)
(let-location ((n double))
  (let ((f ($ double modf (double f) (location n))))
    (cons n f)))
; Returns: (99.0 . 0.2)
```

### Calling Without Return Value

```scheme
($ puts "Hello from C!")
```

### Passing Quoted Literals

```scheme
($ some-c-function (quote "literal string") 42)
```

## Implementation Details

The macro expands to `foreign-lambda*`, `foreign-code`, or `foreign-value` forms depending on context.

## Constraints

**Important:** "Callbacks into Scheme are not allowed inside the invoked foreign code."

This means you cannot pass Scheme procedures as C callbacks using this macro - it's designed for simple foreign function calls only.

## Installation

```bash
chicken-install dollar
```

## See Also

- foreign-lambda (CHICKEN core FFI)
- bind (automatic binding generator)
- easyffi (higher-level FFI wrapper)
