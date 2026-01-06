# Library of Cyberspace Documentation

This directory contains comprehensive documentation for the Library of Cyberspace preservation architecture in multiple formats.

## Documentation Formats

### Man Pages (`*.1`)

Unix manual pages for command-line tools:

- `seal.1` - Vault system (cryptographically sealed version control)
- `audit.1` - Audit trail (content-addressed, chained audit log)

**View with:**
```bash
man ./seal.1
man ./audit.1
```

### Markdown (`*.md`)

- `LIBRARY-OF-CYBERSPACE.md` - Complete architecture documentation

**View with:**
```bash
less LIBRARY-OF-CYBERSPACE.md
# or any markdown viewer
```

### HTML HyperSpec (`hyperspec/`)

Beautiful typeset documentation inspired by the Common Lisp HyperSpec:

- `index.html` - Main entry point with architecture overview
- `symbols.html` - Complete symbol index
- `permuted.html` - Permuted index (find functions by any word)
- `style.css` - Typography and styling (Palatino/Garamond serif fonts)

**View with:**
```bash
open hyperspec/index.html
# or
firefox hyperspec/index.html
```

## Features

### Progressive Documentation

Like the vault's progressive metadata, documentation is available at multiple levels:

1. **Quick reference** - Man pages for command-line lookup
2. **Complete guide** - Markdown for reading and searching
3. **Indexed reference** - HyperSpec for deep exploration

### HyperSpec Highlights

The HyperSpec provides:

- **Symbol Index** - All functions, types, and concepts alphabetically
- **Permuted Index** - Find functions by any significant word
- **Beautiful Typography** - Serif fonts (Palatino/Garamond) for readability
- **Cross-linking** - Navigate between related concepts
- **Print-friendly** - Optimized CSS for printing

### Typography

The HyperSpec uses classic book typography:

- **Body text**: Palatino Linotype, Book Antiqua, Georgia
- **Headings**: Garamond, Times New Roman
- **Code**: Monaco, Menlo, Courier New
- **Colors**: Warm cream background with gold accents
- **Layout**: Centered, max-width for optimal reading

## Building Documentation

The documentation is pre-generated and ready to view. To regenerate:

```bash
# Man pages are written in groff format
# No build step needed - view directly with `man`

# Markdown is plain text
# No build step needed

# HTML is static
# No build step needed - open in browser
```

## Documentation Contents

### Vault System (`seal`)

Cryptographically sealed version control with:

- Core operations (commit, update, undo, history, branch, merge)
- Version management (release, verify, archive, restore, migrate)
- Progressive metadata (minimal, catalog, preserve)
- Archive formats (tarball, bundle, cryptographic)

### Audit Trail (`audit`)

Content-addressed audit logging with:

- Entry creation and verification
- Chain verification
- Query interface (by actor, action, timerange)
- Export formats (S-expression, human-readable)

### SPKI Integration

Simple Public Key Infrastructure:

- Ed25519 keypair generation
- Certificate creation and verification
- Decentralized authorization
- S-expression encoding

## Future Additions

Planned documentation enhancements:

- [ ] Individual function reference pages (linked from symbol index)
- [ ] Tutorial/walkthrough document
- [ ] Architecture diagrams (SVG)
- [ ] Example workflows
- [ ] Troubleshooting guide
- [ ] API reference for programmatic use

## License

This is free software; see the source for copying conditions.

**Library of Cyberspace Preservation Architecture**
*Sealing knowledge for future generations*
