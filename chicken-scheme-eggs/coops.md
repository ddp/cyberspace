# COOPS - CHICKEN Object-Oriented Programming System

**Source:** http://wiki.call-cc.org/eggref/5/coops

**License:** BSD 2-Clause

**Author:** Based on ScmObj by Dorai Sitaram

**Dependencies:** matchable, record-variants

## Overview

COOPS is an object-oriented programming system for CHICKEN Scheme that implements classes with multiple inheritance, generic procedures, and methods that can specialize on one or more arguments.

## Core Features

### Class System

- Define classes using `define-class` syntax with superclass inheritance
- Classes are first-class values, instances of `<standard-class>`
- Support for slot specifications with options (reader, writer, accessor, initform)
- Multiple inheritance capability

### Generic Procedures & Methods

- Create generic procedures with `define-generic` or `define-method`
- Implement multimethods specializing on multiple argument types
- Support for auxiliary methods: before, after, and around methods
- Call-next-method capability in primary and around methods

### Slot Access

- `slot-value` for reading/writing instance slots
- `slot-exists?` to check slot presence
- `slot-initialized?` to verify initialization status

## Key Procedures

| Procedure | Purpose |
|-----------|---------|
| `make` | Create class instances with initialization |
| `class-of` | Return object's class |
| `subclass?` | Test class relationships |
| `initialize-instance` | Generic initialization hook |
| `generic-procedure?` | Check if value is generic |

## Predefined Classes

- `<standard-object>` - Base class for user-defined classes
- `<standard-class>` - Metaclass for all classes
- `<generic-procedure>` - Class of generic procedure objects
- `#t` - Superclass of all classes

## Usage Example

```scheme
(import coops)

;; Define a class
(define-class <stack> ()
  ((content initform: '())))

;; Define methods
(define-method (push (s <stack>) item)
  (slot-set! s 'content (cons item (slot-ref s 'content))))

(define-method (pop (s <stack>))
  (let ((items (slot-ref s 'content)))
    (if (null? items)
        (error "Stack is empty")
        (begin
          (slot-set! s 'content (cdr items))
          (car items)))))

;; Create and use an instance
(define my-stack (make <stack>))
(push my-stack 'a)
(push my-stack 'b)
(pop my-stack)  ; => b
```

## Class Definition Syntax

```scheme
(define-class class-name (superclass ...)
  (slot-spec ...)
  metaclass: metaclass)
```

**Slot specification options:**

- `reader:` - Create a reader method
- `writer:` - Create a writer method
- `accessor:` - Create both reader and writer
- `initform:` - Default initial value
- `init-keyword:` - Keyword for make initialization

## Generic Procedure Definition

```scheme
(define-generic procedure-name)

(define-method (procedure-name (arg1 <class1>) (arg2 <class2>) ...)
  body ...)
```

## Method Combinations

### Primary Methods

Standard method dispatch based on argument types.

### Before Methods

```scheme
(define-method (initialize-instance before: (obj <my-class>) initargs)
  ;; Runs before primary method
  )
```

### After Methods

```scheme
(define-method (initialize-instance after: (obj <my-class>) initargs)
  ;; Runs after primary method
  )
```

### Around Methods

```scheme
(define-method (some-method around: (obj <my-class>) args)
  ;; Can call (call-next-method) to invoke next method
  ;; or bypass it entirely
  )
```

## Initialization & Extensions

### Primitive Objects Extension

Import `coops-primitive-objects` to provide primitive classes for built-in types, enabling generic dispatch on native Scheme values:

```scheme
(import coops coops-primitive-objects)

(define-method (double (x <number>))
  (* x 2))

(define-method (double (s <string>))
  (string-append s s))

(double 5)      ; => 10
(double "hi")   ; => "hihi"
```

**Primitive classes include:**
- `<list>`, `<pair>`, `<null>`
- `<vector>`
- `<number>`, `<integer>`, `<real>`, `<complex>`
- `<string>`, `<char>`
- `<boolean>`, `<symbol>`
- `<procedure>`
- And more

## Installation

```bash
chicken-install coops
```

## See Also

- CLOS (Common Lisp Object System) - inspiration
- prometheus (prototype-based alternative)
- TinyCLOS (ancestor project)
