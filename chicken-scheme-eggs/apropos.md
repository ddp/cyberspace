# Apropos - Symbol Search Facility

**Source:** http://wiki.call-cc.org/eggref/5/apropos

**License:** BSD-style MIT

**Dependencies:** utf8, srfi-1, check-errors, symbol-utils

## Overview

The apropos egg provides a search facility for CHICKEN Scheme, allowing users to discover symbols matching specified patterns in the toplevel environment.

## Core API

### Main Procedures

#### `apropos`

Displays information about matching symbols with options for sorting, case sensitivity, and filtering.

**Parameters:**

- `PATTERN` - Symbol, string, or regex for matching
- `MACROS?` - Include macro definitions (default: `#f`)
- `SORT` - Sort by `#:name`, `#:module`, `#:type`, or `#f` (default: `#:type`)
- `CASE-INSENSITIVE?` - Enable case-insensitive matching (default: `#f`)
- `BASE` - Number base 2-16 for pattern conversion (default: `10`)
- `INTERNAL?` - Include internal modules (default: `#f`)
- `IMPORTED?` - Filter imported identifiers only (default: `#f`)

**Example:**

```scheme
(apropos "cons")
(apropos "map" macros?: #t sort: #:name)
(apropos "string" case-insensitive?: #t)
```

#### `apropos-list`

Returns unsorted matching symbols as a list instead of displaying them.

```scheme
(apropos-list PATTERN . OPTIONS)
```

#### `apropos-information-list`

Returns symbol metadata keyed by `(MODULE . NAME)` pairs, with values indicating type:
- `'macro` - Macro definition
- `'keyword` - Keyword
- `'variable` - Variable
- `'procedure` - Procedure
- Procedure specifications with arity information

```scheme
(apropos-information-list PATTERN . OPTIONS)
```

### Parameters

#### `apropos-excluded-modules`

Exclude identifiers from modules matching specified prefixes. Accepts symbolic or string input.

```scheme
(apropos-excluded-modules '(chicken.internal))
```

#### `apropos-default-base`

Set default numeric base (2-16) for pattern conversion.

```scheme
(apropos-default-base 16)
```

#### `apropos-default-options`

Configure default keyword arguments for apropos operations.

```scheme
(apropos-default-options '(sort: #:name case-insensitive?: #t))
```

#### `apropos-interning`

Choose between `string->symbol` (`#t`) or `string->uninterned-symbol` (`#f`).

```scheme
(apropos-interning #f)
```

## CSI Integration

When loaded, apropos-csi adds a `,a` toplevel command accepting pattern and options:

**Options:**
- `macros` or `mac` - Include macro definitions
- `sort [name|module|type|#f]` - Set sorting strategy
- `find [name|module|#f]` - Match scope
- `case-insensitive` or `ci` - Enable case-insensitive search
- `base 2..16` - Set numeric base
- `internal` - Include internal modules

**Example:**

```scheme
,a cons
,a map macros sort name
,a string ci
```

## Known Limitations

- Renamed or prefixed module imports won't match using import aliases
- Macro introspection lacks detailed meta-information beyond transformer procedures
- Macro support implementation relies on core machinery assumptions

## Installation

```bash
chicken-install apropos
```

## See Also

- symbol-utils (dependency)
- chicken-doc (documentation lookup)
