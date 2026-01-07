# RFC-019: Documentation Pipeline

**Status:** Implemented
**Date:** January 2026
**Author:** Derrell Piper <ddp@eludom.net>
**Implementation:** generate-rfcs.sh

---

## Abstract

This RFC specifies the documentation pipeline for the Library of Cyberspace: automated generation of canonical document formats, index catalogs, and future syndication feeds.

---

## Motivation

Documentation must be:

1. **Preserved** - Multiple formats for long-term archival
2. **Accessible** - Viewable in any environment
3. **Discoverable** - Indexed for navigation
4. **Syndicated** - Subscribable for updates (future)

The pipeline automates generation of all canonical formats from Markdown source.

---

## Canonical Formats

| Format | Extension | Purpose | Tool |
|--------|-----------|---------|------|
| Markdown | `.md` | Source, editing, version control | - |
| HTML | `.html` | Web viewing, rich rendering | pandoc --standalone |
| PDF | `.pdf` | Archival, printing, distribution | pandoc + xelatex |
| Plain Text | `.txt` | Universal compatibility, IETF tradition | pandoc --to=plain |

All formats are first-class citizens. None is derived or secondary.

---

## Pipeline Specification

### Input

Markdown source files following the naming convention:
```
rfc-NNN-short-name.md
```

Where:
- `NNN` - Zero-padded RFC number (000-999)
- `short-name` - Lowercase, hyphenated descriptive name

### Output

For each input file, generate:
```
rfc-NNN-short-name.html   # Standalone HTML
rfc-NNN-short-name.pdf    # PDF via XeLaTeX
rfc-NNN-short-name.txt    # Plain text, 78 columns
```

Plus a navigational index:
```
index.html                # Hypertext catalog
```

### Generation Commands

```bash
# HTML (standalone, no external dependencies)
pandoc ${rfc}.md -o ${rfc}.html --standalone --metadata title=""

# PDF (XeLaTeX with monospace font for code)
pandoc ${rfc}.md -o ${rfc}.pdf --pdf-engine=xelatex -V mainfont="Menlo"

# Plain text (IETF-style, 78 columns)
pandoc ${rfc}.md -o ${rfc}.txt --to=plain --wrap=auto --columns=78
```

### Index Generation

The index.html catalog provides:

- RFC number and title
- Links to all four formats
- Clean, accessible HTML

Structure:
```html
<table>
  <tr>
    <td>RFC Number</td>
    <td>Title</td>
    <td>html | pdf | txt | md</td>
  </tr>
</table>
```

---

## Publication

### Local Workflow

```bash
# Generate all formats
./generate-rfcs.sh

# Commit to vault
seal-commit "Regenerate RFC documentation"
```

### Remote Publication

```bash
# Publish to web server
rsync -avz --chmod=D755,F644 -e ssh \
  *.md *.html *.pdf *.txt index.html \
  user@server:~/path/to/docs/
```

Permission model:
- Directories: 755 (world-readable, owner-writable)
- Files: 644 (world-readable, owner-writable)

---

## Future: Syndication

### RSS/Atom Feeds

Future versions will generate:

```
rfc-feed.xml    # Atom feed of RFC updates
```

Feed entries will include:
- RFC number and title
- Publication/update date
- Abstract
- Links to all formats

### Subscription Model

```scheme
;; Subscribe to RFC feed
(seal-subscribe "https://example.com/cyberspace/rfc-feed.xml"
  verify-key: publisher-public)
```

Integration with Vault subscription system (RFC-006).

---

## Implementation

### generate-rfcs.sh

```bash
#!/bin/bash
# RFC Documentation Pipeline

RFCS=(rfc-000-manifesto rfc-001-replication-layer ...)

for rfc in "${RFCS[@]}"; do
  pandoc "${rfc}.md" -o "${rfc}.html" --standalone
  pandoc "${rfc}.md" -o "${rfc}.pdf" --pdf-engine=xelatex -V mainfont="Menlo"
  pandoc "${rfc}.md" -o "${rfc}.txt" --to=plain --columns=78
done

# Generate index.html
generate_index
```

### Dependencies

| Tool | Version | Purpose |
|------|---------|---------|
| pandoc | 2.x+ | Document conversion |
| xelatex | TeX Live | PDF generation |
| rsync | 3.x+ | Publication |

---

## Security Considerations

### Integrity

Generated documents inherit integrity from:
- Git version control (source)
- Vault signatures (releases)

### Publication

Remote publication uses:
- SSH key authentication
- No sensitive data in documents
- World-readable permissions only

---

## References

1. [Pandoc User's Guide](https://pandoc.org/MANUAL.html)
2. [RFC-006](rfc-006-vault-architecture.md) - Vault System Architecture
3. [Atom Syndication Format](https://tools.ietf.org/html/rfc4287) - RFC 4287

---

## Changelog

- **2026-01-06** - Initial specification

---

**Implementation Status:** Complete
**Script:** generate-rfcs.sh
**Formats:** Markdown, HTML, PDF, Plain Text
