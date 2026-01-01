# big-chicken - Core Library Convenience Wrapper

**Source:** http://wiki.call-cc.org/eggref/5/big-chicken

**License:** Public domain

**Author:** felix winkelmann

**Repository:** https://anonymous@code.call-cc.org/svn/chicken-eggs/release/5/big-chicken

## Overview

The big-chicken egg is a CHICKEN Scheme extension that provides a convenience wrapper for core library modules. As described: "Are you tired of writing (import (chicken base) (chicken bitwise) (chicken blob) yaddda yadda..."

## Purpose

This extension simplifies imports by bundling all core `(chicken *)` modules into a single convenience package, eliminating the need to manually specify individual library units.

## Usage

Instead of:

```scheme
(import (chicken base)
        (chicken bitwise)
        (chicken blob)
        (chicken condition)
        (chicken file)
        ...)
```

Simply use:

```scheme
(import big-chicken)
```

## Version History

- **1.1** - Re-exported chicken.irregex
- **1.0** - Initial release for CHICKEN 5
- **0.4** - Added regex dependency
- **0.3** - Fixed syntax-reexport issue
- **0.2** - Corrected setup script typo
- **0.1** - Original release

## Installation

```bash
chicken-install big-chicken
```

## Notes

This is a convenience wrapper only - no additional functionality is provided beyond simplifying imports of the core CHICKEN libraries.
