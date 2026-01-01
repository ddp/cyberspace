# utf8 - Unicode Support for CHICKEN Scheme

**Source:** http://wiki.call-cc.org/eggref/5/utf8

**License:** BSD 3-Clause

**Author:** Alex Shinn

**Version:** 3.5.0 (CHICKEN 5)

## Overview

The utf8 egg provides "Unicode support" for CHICKEN Scheme, enabling Unicode-aware string operations throughout the language.

## Core Features

### Basic Integration

```scheme
(import utf8)
```

Enables Unicode awareness across core, extra, and regex string operations:
- String length calculations return **codepoint counts** rather than byte counts
- String indexing works with **codepoints** instead of bytes
- Regular expressions become Unicode-aware

### String Compatibility

**Important:** "Strings are still native strings and may be passed to external libraries (either Scheme or foreign) perfectly safely."

This design avoids creating incompatible string types that fragment library ecosystems (as seen in C and early Perl implementations).

## API Modules

### Main Modules

#### `utf8`

Core Unicode string operations - replaces standard string procedures with Unicode-aware versions.

#### `utf8-srfi-13`

SRFI-13 string procedures with Unicode semantics.

```scheme
(import utf8-srfi-13)
```

Provides Unicode-aware versions of:
- `string-upcase`, `string-downcase`, `string-titlecase`
- `string-length`, `string-ref`, `string-set!`
- `string-contains`, `string-split`
- And all other SRFI-13 procedures

#### `utf8-srfi-14`

SRFI-14 character set procedures.

```scheme
(import utf8-srfi-14)
```

#### `utf8-case-map`

Locale-aware case conversion.

```scheme
(import utf8-case-map)

(string-upcase "hello")                  ; => "HELLO"
(string-downcase "WORLD")                ; => "world"
(string-titlecase "hello world")         ; => "Hello World"
```

#### `unicode-char-sets`

Full Unicode character set definitions.

```scheme
(import unicode-char-sets)
```

Provides over 100 Unicode property-based character sets.

#### `utf8-lolevel`

Low-level UTF-8 encoding manipulation.

```scheme
(import utf8-lolevel)
```

### Namespace Management

The module requires excluding conflicting identifiers from standard imports:

```scheme
(import (except scheme
                string-length string-ref string-set!
                string->list list->string
                string-upcase string-downcase))

(import (except chicken.base
                string-length string-ref string-set!))

(import (except chicken.string
                string-split string-translate))

(import utf8)
```

## Key Capabilities

### Unicode Character Sets

Over 100 Unicode property-based character sets available:

**Alphabetic:**
- `char-set:alphabetic`
- `char-set:letter`
- `char-set:lowercase`
- `char-set:uppercase`
- `char-set:titlecase`

**Script-specific:**
- `char-set:greek`
- `char-set:han` (Chinese characters)
- `char-set:hiragana`
- `char-set:katakana`
- `char-set:cyrillic`
- `char-set:armenian`
- `char-set:bengali`
- `char-set:tamil`
- `char-set:thai`
- And many more...

**Categories:**
- `char-set:numeric`
- `char-set:punctuation`
- `char-set:symbol`
- `char-set:whitespace`

### Performance Characteristics

**Important:** "string-length, string-ref and string-set! are all O(n) operations as opposed to the usual O(1)" due to variable-width UTF-8 encoding.

**Recommendation:** Use high-level SRFI-13 procedures for better performance when working with multiple operations.

## Usage Examples

### Basic String Operations

```scheme
(import utf8)

;; Length in codepoints, not bytes
(string-length "hello")                  ; => 5
(string-length "こんにちは")              ; => 5 (not 15 bytes)

;; Index by codepoints
(string-ref "hello" 1)                   ; => #\e
(string-ref "こんにちは" 1)               ; => こ
```

### Case Conversion

```scheme
(import utf8-case-map)

(string-upcase "Straße")                 ; => "STRASSE" (German ß)
(string-downcase "ΣΕΛΛΑΣ")               ; => "σελλας" (Greek)
(string-titlecase "istanbul")            ; => "İstanbul" (Turkish)
```

### Character Set Matching

```scheme
(import utf8)
(import unicode-char-sets)

(char-set-contains? char-set:greek #\α)  ; => #t
(char-set-contains? char-set:han #\漢)   ; => #t

;; Filter characters
(string-filter char-set:numeric "abc123def456")
; => "123456"
```

### Working with Multiple Scripts

```scheme
(import utf8)
(import unicode-char-sets)

(define mixed "Hello世界مرحبا")

;; Count by script
(string-count mixed char-set:han)        ; => 2 (世界)
(string-count mixed char-set:arabic)     ; => 5 (مرحبا)
(string-count mixed char-set:alphabetic) ; => 5 (Hello)
```

### String Manipulation

```scheme
(import utf8-srfi-13)

(string-contains "こんにちは世界" "世界")  ; => 5
(string-split "α β γ δ" " ")             ; => ("α" "β" "γ" "δ")
(string-trim "  hello  ")                ; => "hello"
```

### Regular Expressions

```scheme
(import utf8)
(import (chicken irregex))

;; Unicode-aware regex
(irregex-search '(* alpha) "hello世界")
; Matches Unicode alphabetic characters
```

## Notable Limitations

### Incomplete Coverage

Some procedures lack Unicode versions:
- `string-chomp` - Not Unicode-aware
- `printf` - Byte-oriented
- `read-line` - Byte-oriented
- `pretty-print` - Not fully Unicode-aware

### Low-level Operations

- `peek-char` operates at byte-level only
- Character sets aren't interchangeable between Unicode and non-Unicode code

## Design Philosophy

The extension modifies operations on existing string types rather than creating new Unicode string types.

**Advantage:** Avoids the "schism" problems where incompatible string types fragment libraries and make code harder to compose.

**Trade-off:** Performance penalty for random access (O(n) instead of O(1)) due to UTF-8's variable-width encoding.

## Complete Example

```scheme
;; Import with proper exclusions
(import (except scheme
                string-length string-ref string-set!))
(import (except chicken.base
                string-length string-ref string-set!))
(import utf8)
(import utf8-srfi-13)
(import utf8-case-map)
(import unicode-char-sets)

;; Unicode string processing
(define greetings
  '("Hello"
    "こんにちは"
    "مرحبا"
    "Здравствуйте"
    "你好"))

;; Count characters (not bytes)
(for-each
  (lambda (s)
    (printf "~A: ~A characters~%"
            s
            (string-length s)))
  greetings)

;; Case conversion
(printf "Uppercase: ~A~%" (string-upcase "Straße"))
(printf "Lowercase: ~A~%" (string-downcase "МОСКВА"))

;; Character set filtering
(define mixed "abc123αβγ456")
(printf "Numbers only: ~A~%"
        (string-filter char-set:numeric mixed))
(printf "Greek only: ~A~%"
        (string-filter char-set:greek mixed))
```

## Installation

```bash
chicken-install utf8
```

## See Also

- SRFI-13 (string library)
- SRFI-14 (character sets)
- Unicode Standard (unicode.org)
- utf8-srfi-13 (Unicode-aware SRFI-13)
