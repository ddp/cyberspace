# Prometheus - Prototype-based Object System

**Source:** https://wiki.call-cc.org/eggref/5/prometheus?action=show&rev=43782

**License:** BSD 3-Clause

**Author:** Jörgen Schäfer (original), Daniel Ziltener (CHICKEN 5 port)

**Dependencies:** SRFI-1

## Overview

Prometheus is a prototype-based message-passing object system for CHICKEN Scheme inspired by the Self language. It implements objects as collections of slots that respond to messages through an inheritance hierarchy.

## Core Concepts

### Objects and Messages

A message consists of a symbol called a selector, and zero or more arguments. Objects respond by searching for matching slots, with inheritance through parent slots when handlers aren't found locally.

### Prototype-based Creation

Objects are created by cloning existing objects, producing new instances with a parent slot pointing to the prototype. This allows behavior modification before cloning production instances.

## Hermes Foundation

Prometheus is built on Hermes, which provides the underlying message system.

### Core Procedure

```scheme
(make-hermes-object)
```

Creates a new Hermes object with basic message capabilities.

### Key Hermes Messages

- `add-message!` - Registers message handlers
- `delete-message!` - Removes handlers
- `%get-handler` - Core inheritance lookup returning handler and source object

## Prometheus API

### Root Objects

#### `make-prometheus-root-object`

Creates independent object hierarchies.

#### `*the-root-object*`

Default root object for most applications.

### Root Object Messages

#### `clone`

Creates object copies with parent pointer.

```scheme
(obj 'clone)
```

#### `add-value-slot!`

```scheme
(obj 'add-value-slot! getter [setter] value)
```

Adds a slot that stores and returns data.

#### `add-method-slot!`

```scheme
(obj 'add-method-slot! getter proc)
```

Adds a slot containing a procedure.

#### `add-parent-slot!`

```scheme
(obj 'add-parent-slot! getter parent)
```

Adds a parent slot for inheritance.

#### `delete-slot!`

```scheme
(obj 'delete-slot! name)
```

Removes a slot from the object.

#### `immediate-slot-list`

```scheme
(obj 'immediate-slot-list)
```

Returns slot information.

#### Error Handlers

- `message-not-understood` - Called when no handler is found
- `ambiguous-message-send` - Called when multiple inheritance creates ambiguity

### Slot Types

**Value slots** store and return data values.

**Method slots** contain procedures that receive:
- `self` - The object that received the message
- `resend` - Function to call parent handlers
- Additional message arguments

**Parent slots** enable inheritance searches.

## Syntactic Sugar

### `define-method`

Shorthand for adding method slots.

```scheme
(define-method (obj 'message self resend args ...)
  body ...)
```

Equivalent to:

```scheme
(obj 'add-method-slot! 'message
  (lambda (self resend args ...)
    body ...))
```

### `define-object`

Combines cloning with slot creation.

```scheme
(define-object name (parent)
  (slot-name value)           ; value slot
  ((method self resend args)  ; method slot
    body ...))
```

## Inheritance and Resend

When methods don't handle messages locally, `resend` allows delegating to parent handlers. When a message is sent to an object, methods receive that object as the `self` argument. Resend ensures correct `self` binding in parent methods.

### `resend` accepts:

- `#f` - Search any parent of current handler's object
- Symbol - Search specific named parent slot
- Object - Send directly to target object

## Usage Examples

### Simple Account Object

```scheme
(use prometheus)

(define account
  (*the-root-object* 'clone))

(define-method (account 'init self resend balance)
  (self 'add-value-slot! 'balance 'balance! balance))

(define-method (account 'deposit! self resend amount)
  (self 'balance! (+ (self 'balance) amount)))

(define-method (account 'withdraw! self resend amount)
  (self 'balance! (- (self 'balance) amount)))

;; Usage
(define my-account (account 'clone))
(my-account 'init 1000)
(my-account 'deposit! 500)
(my-account 'balance)  ; => 1500
```

### Dynamic Slot Creation

```scheme
(define-method (obj 'message-not-understood self resend selector . args)
  (if (null? args)
      (begin
        (self 'add-value-slot! selector (string->symbol
                                          (string-append (symbol->string selector) "!"))
                              #f)
        (self selector))
      (resend #f selector args)))
```

## Key Pitfalls

### Multiple Inheritance Ambiguity

Diamond inheritance patterns risk ambiguous message sends when the same slot appears through multiple parents. Setters added to child objects create new message paths, potentially conflicting with inherited setters.

### Private Messages

Non-symbol message names (fresh lists, etc.) enable privacy since only code with references can target them.

```scheme
(define private-msg (list 'private))
(obj 'add-method-slot! private-msg (lambda (self resend) ...))
```

## Installation

```bash
chicken-install prometheus
```

## See Also

- Hermes (underlying message system)
- SRFI-1 (list processing dependency)
- Self language (inspiration)
