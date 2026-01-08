# RFC-019: Documentation Pipeline

**Status:** Implemented
**Date:** January 2026
**Author:** Derrell Piper <ddp@eludom.net>
**Implementation:** generate-rfcs.sh

---

## Abstract

This RFC specifies the documentation pipeline for the Library of Cyberspace: automated generation of canonical document formats and index catalogs. Output formats are HTML, PostScript, and plain text—open formats that will outlast corporations.

---

## Motivation

Documentation must be:

1. **Preserved** - Open formats for long-term archival
2. **Accessible** - Viewable in any environment
3. **Readable** - Human-readable output
4. **Discoverable** - Indexed for navigation

### Why PostScript, Not PDF

PDF is Adobe's proprietary format dressed in ISO clothing.[^h1] PostScript is:

- **Open** - Published specification since 1984
- **Stable** - Level 3 unchanged since 1997
- **Readable** - Plain text you can grep, diff, edit
- **Honest** - Describes rendering, doesn't control viewing

NeXT got it right. The source is the document.[^h2]

[^h1]: Historical: Adobe created PDF in 1993 as a proprietary format, then
donated it to ISO in 2008 (ISO 32000) after market dominance was achieved.
The "open standard" arrived after lock-in.

[^h2]: Historical: NeXT's Display PostScript (1988) used PostScript as the
native imaging model. What you saw on screen was what the printer rendered.
Steve Jobs understood that the document format *is* the document.

---

## Footnote Categories

RFCs use categorized footnotes to separate different types of annotations:[^d2]

*Table 2: Footnote Categories*

| Prefix | Category | Purpose |
|--------|----------|---------|
| `[^d]` | Design | Rationale, trade-offs, alternatives considered |
| `[^r]` | Research | Academic references, papers, formal methods |
| `[^h]` | Historical | Context, predecessors, lessons from past systems |
| `[^i]` | Implementation | Code notes, performance, optimization details |

**Convention:** Number sequentially within category (e.g., `[^d1]`, `[^d2]`, `[^h1]`, `[^h2]`).[^r1]

[^d2]: Design: Categorized footnotes prevent mixing implementation details
with historical context. Readers can skim by category.

[^r1]: Research: Knuth's literate programming separates code from
documentation. Our footnote categories extend this to separate
design rationale from historical context from implementation notes.
See Knuth, "Literate Programming" (1984).

---

## Output Formats

*Table 1: Output Formats*

| Format | Extension | Purpose |
|--------|-----------|---------|
| Text | `.txt` | IETF tradition, universal, immortal |
| PostScript | `.ps` | Archival, printing |
| Hypertext Markup Language | `.html` | Web viewing |

**Philosophy:** Text, PostScript, and Hypertext Markup Language cover all use cases with open formats. No proprietary gatekeepers. These three are canonical—don't add more.[^d1]

[^d1]: Design: Three formats cover all use cases. Text is grep-able and
eternal. PostScript is printable and archival. HTML is web-viewable.
Adding PDF would be redundant (PostScript covers printing) and would
introduce a proprietary dependency.

---

## Pipeline Specification

### Output

For each RFC:
```
rfc-NNN-short-name.html   # Standalone HTML
rfc-NNN-short-name.ps     # PostScript
rfc-NNN-short-name.txt    # Plain text, 78 columns
```

Plus a navigational index:
```
index.html                # Hypertext catalog
```

### Generation

```bash
./generate-rfcs.sh
```

The script handles all format generation automatically.

### Table of Contents

Each RFC generates a table of contents from section headings:[^i1]

- Level 1: `#` - RFC title (not in TOC)
- Level 2: `##` - Major sections
- Level 3: `###` - Subsections

HTML output includes navigable TOC with anchor links.

[^i1]: Implementation: Pandoc generates TOC with `--toc` flag.
PostScript uses LaTeX `\tableofcontents`. Plain text uses
indented section listing.

### Index Generation

The index.html catalog provides:

- RFC number and title
- Links to all output formats (html, ps, txt)
- Clean, accessible HTML

Structure:
```html
<table>
  <tr>
    <td>RFC Number</td>
    <td>Title</td>
    <td>html | ps | txt</td>
  </tr>
</table>
```

### Permuted Index (KWIC)

A Key Word In Context index rotates titles around each significant word:[^h3]

```
              Architecture  RFC-002: Vault System Architecture
                    Audit  RFC-003: Cryptographic Audit Trail
Vault System  Architecture  RFC-002: Vault System Architecture
Cryptographic       Audit  RFC-003: Cryptographic Audit Trail
```

**Stop words excluded:** a, an, and, for, in, of, on, or, the, to, with

The permuted index enables discovery by concept rather than by RFC number.[^r2]

[^h3]: Historical: KWIC indices originated at IBM (1958) for chemical
abstracts. Unix `ptx` command generates permuted indices. The technique
predates full-text search and remains valuable for browsable discovery.

[^r2]: Research: Luhn, H.P. "Keyword-in-Context Index for Technical
Literature (KWIC Index)" (1960). American Documentation 11(4):288-295.

---

## Publication

### Pipeline Vocabulary

```
commit  →  sync  →  publish
  │         │         │
  git     github   yoyodyne
 local    remote      www
```

*Table 3: Publication Commands*

| Command | Action | Target |
|---------|--------|--------|
| `commit` | `git commit` | Local repository |
| `sync` | `git pull && git push` | GitHub (cyberspace) |
| `publish` | `rsync` | Yoyodyne (www) |

**Note:** `sync` is intentionally ambiguous—it also means lazy clustering sync (RFC-016). Context disambiguates. The ambiguity with git is preserved.[^d3]

[^d3]: Design: Overloaded vocabulary reflects reality. "Sync" universally means
bidirectional reconciliation. Fighting this creates cognitive load. Embrace it.

### Commit (Local)

```bash
# Generate all formats
./generate-rfcs.sh

# Commit to vault
git add -A && git commit -m "Regenerate RFC documentation"
```

### Sync (GitHub)

```bash
# Sync with remote
git pull && git push
```

### Publish (Yoyodyne)

```bash
# Publish to yoyodyne
rsync -avz --chmod=D755,F644 \
  *.html *.ps *.txt \
  ddp@www.yoyodyne.com:/www/yoyodyne/ddp/cyberspace/
```

**Published URL:** https://www.yoyodyne.com/ddp/cyberspace/

**Published:**
- `*.html` - Web viewing
- `*.ps` - PostScript (archival, printing)
- `*.txt` - Plain text
- `index.html` - Catalog

Permission model:
- Directories: 755 (world-readable, owner-writable)
- Files: 644 (world-readable, owner-writable)

---

## Dependencies

| Tool | Version | Purpose |
|------|---------|---------|
| pandoc | 2.x+ | Document conversion |
| latex | TeX Live | DVI generation |
| dvips | TeX Live | DVI → PostScript |
| rsync | 3.x+ | Publication |

PostScript viewers: TeXShop, Preview, Ghostscript, or read the source directly.

---

## Security Considerations

### Integrity

Generated documents inherit integrity from:
- Git version control
- Vault signatures (releases)

### Publication

Remote publication uses:
- SSH key authentication
- No sensitive data in documents
- World-readable permissions only

---

## References

1. Pandoc User's Guide *(preserved)*
2. PostScript Language Reference Manual - Adobe *(preserved)*
3. RFC-006: Vault System Architecture

---

## Changelog

- **2026-01-07** - Add footnote categories, TOC, permuted index (KWIC)
- **2026-01-07** - Replace PDF with PostScript (open format)
- **2026-01-06** - Initial specification

---

**Implementation Status:** Complete
**Script:** generate-rfcs.sh
**Output Formats:** HTML, PostScript, Plain Text
