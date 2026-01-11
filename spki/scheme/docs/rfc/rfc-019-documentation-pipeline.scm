;; Auto-converted from Markdown
;; Review and edit as needed

(rfc
  (number 19)
  (title "Documentation Pipeline")
  (section
    "Abstract"
    (p "This RFC specifies the documentation pipeline for the Library of Cyberspace: automated generation of canonical document formats and index catalogs. Output formats are HTML, PostScript, and plain text—open formats that will outlast corporations."))
  (section
    "Motivation"
    (p "Documentation must be:")
    (p "1. Preserved - Open formats for long-term archival 2. Accessible - Viewable in any environment 3. Readable - Human-readable output 4. Discoverable - Indexed for navigation")
    (subsection
      "Why PostScript, Not PDF"
      (p "PDF is Adobe's proprietary format dressed in ISO clothing.[^h1] PostScript is:")
      (p "- Open - Published specification since 1984 - Stable - Level 3 unchanged since 1997 - Readable - Plain text you can grep, diff, edit - Honest - Describes rendering, doesn't control viewing")
      (p "NeXT got it right. The source is the document.[^h2]")
      (p "[^h1]: Historical: Adobe created PDF in 1993 as a proprietary format, then donated it to ISO in 2008 (ISO 32000) after market dominance was achieved. The \"open standard\" arrived after lock-in.")
      (p "[^h2]: Historical: NeXT's Display PostScript (1988) used PostScript as the native imaging model. What you saw on screen was what the printer rendered. Steve Jobs understood that the document format is the document.")))
  (section
    "RFC Categories"
    (p "Following IETF tradition (RFC 2026, RFC 2223).[^d4]")
    (p "Table 0: RFC Categories and Authorship")
    (table
      (header "Category " "Description " "Author ")
      (row "Standards Track " "Core specifications defining the system " "Core maintainers ")
      (row "Informational " "Guidelines, explanations, tutorials " "Anyone in federation ")
      (row "Experimental " "New ideas being tested " "Anyone in federation ")
      (row "Best Current Practice " "Recommended approaches " "Core maintainers ")
      (row "Historic " "Deprecated specifications " "Core maintainers "))
    (p "Open Authorship: Any member of the federation may author Informational or Experimental RFCs. Standards Track, Best Current Practice, and Historic designations require core maintainer approval.")
    (p "[^d4]: Design: Following IETF tradition (RFC 2026). Informational RFCs lower the barrier to contribution while Standards Track maintains architectural coherence. The federation grows through documentation."))
  (section
    "RFC Header Format"
    (p "Every RFC begins with a standardized header block:")
    (code markdown "# RFC-NNN: Title\n\nStatus: Draft | Proposed | Implemented | Historic\nCategory: Standards Track | Informational | Experimental | BCP | Historic\nCreated: YYYY-MM-DD\nUpdated: YYYY-MM-DD\nAuthor: Name <email>\nUpdates: RFC-NNN (if applicable)\nObsoletes: RFC-NNN (if applicable)\n\n---\n\n## Abstract\n\nOne paragraph summary of the RFC.\n\n---\n\n## Status of This Memo\n\nThis document specifies a [Standards Track/Informational/Experimental]\nprotocol for the Library of Cyberspace community.\n\nDistribution of this memo is unlimited.")
    (subsection
      "Status Values"
      (table
        (header "Status " "Meaning ")
        (row "Draft " "Work in progress, not yet reviewed ")
        (row "Proposed " "Under review, seeking feedback ")
        (row "Implemented " "Specification complete, implementation exists ")
        (row "Historic " "Superseded or deprecated ")))
    (subsection
      "Required Sections"
      (p "1. Abstract — One paragraph summary 2. Motivation — Why this RFC exists 3. Specification — The technical details 4. Security Considerations — Required, even if \"None\" 5. References — Citations and dependencies")))
  (section
    "Footnote Categories"
    (p "RFCs use categorized footnotes to separate different types of annotations:[^d2]")
    (p "Table 2: Footnote Categories")
    (table
      (header "Prefix " "Category " "Purpose ")
      (row "[^d] " "Design " "Rationale, trade-offs, alternatives considered ")
      (row "[^r] " "Research " "Academic references, papers, formal methods ")
      (row "[^h] " "Historical " "Context, predecessors, lessons from past systems ")
      (row "[^i] " "Implementation " "Code notes, performance, optimization details "))
    (p "Convention: Number sequentially within category (e.g., [^d1], [^d2], [^h1], [^h2]).[^r1]")
    (p "[^d2]: Design: Categorized footnotes prevent mixing implementation details with historical context. Readers can skim by category.")
    (p "[^r1]: Research: Knuth's literate programming separates code from documentation. Our footnote categories extend this to separate design rationale from historical context from implementation notes. See Knuth, \"Literate Programming\" (1984)."))
  (section
    "Output Formats"
    (p "Table 1: Output Formats")
    (table
      (header "Format " "Extension " "Purpose ")
      (row "Text " ".txt " "IETF tradition, universal, immortal ")
      (row "PostScript " ".ps " "Archival, printing ")
      (row "Hypertext Markup Language " ".html " "Web viewing "))
    (p "Philosophy: Text, PostScript, and Hypertext Markup Language cover all use cases with open formats. No proprietary gatekeepers. These three are canonical—don't add more.[^d1]")
    (p "[^d1]: Design: Three formats cover all use cases. Text is grep-able and eternal. PostScript is printable and archival. HTML is web-viewable. Adding PDF would be redundant (PostScript covers printing) and would introduce a proprietary dependency."))
  (section
    "Pipeline Specification"
    (subsection
      "Output"
      (p "For each RFC:")
      (code "rfc-NNN-short-name.html   # Standalone HTML\nrfc-NNN-short-name.ps     # PostScript\nrfc-NNN-short-name.txt    # Plain text, 78 columns")
      (p "Plus a navigational index:")
      (code "index.html                # Hypertext catalog"))
    (subsection
      "Generation"
      (code bash "./generate-rfcs.sh")
      (p "The script handles all format generation automatically."))
    (subsection
      "Table of Contents"
      (p "Each RFC generates a table of contents from section headings:[^i1]")
      (p "- Level 1: # - RFC title (not in TOC) - Level 2: ## - Major sections - Level 3: ### - Subsections")
      (p "HTML output includes navigable TOC with anchor links.")
      (p "[^i1]: Implementation: Pandoc generates TOC with --toc flag. PostScript uses LaTeX \\tableofcontents. Plain text uses indented section listing."))
    (subsection
      "Index Generation"
      (p "The index.html catalog provides:")
      (p "- RFC number and title - Links to all output formats (html, ps, txt) - Clean, accessible HTML")
      (p "Structure:")
      (code html "<table>\n  <tr>\n    <td>RFC Number</td>\n    <td>Title</td>\n    <td>html | ps | txt</td>\n  </tr>\n</table>"))
    (subsection
      "Permuted Index (KWIC)"
      (p "A Key Word In Context index rotates titles around each significant word:[^h3]")
      (code "              Architecture  RFC-002: Vault System Architecture\n                    Audit  RFC-003: Cryptographic Audit Trail\nVault System  Architecture  RFC-002: Vault System Architecture\nCryptographic       Audit  RFC-003: Cryptographic Audit Trail")
      (p "Stop words excluded: a, an, and, for, in, of, on, or, the, to, with")
      (p "The permuted index enables discovery by concept rather than by RFC number.[^r2]")
      (p "[^h3]: Historical: KWIC indices originated at IBM (1958) for chemical abstracts. Unix ptx command generates permuted indices. The technique predates full-text search and remains valuable for browsable discovery.")
      (p "[^r2]: Research: Luhn, H.P. \"Keyword-in-Context Index for Technical Literature (KWIC Index)\" (1960). American Documentation 11(4):288-295.")))
  (section
    "Publication"
    (subsection
      "Pipeline Vocabulary"
      (code "commit  →  sync  →  publish\n  │         │         │\n  git     github   yoyodyne\n local    remote      www")
      (p "Table 3: Publication Commands")
      (table
        (header "Command " "Action " "Target ")
        (row "commit " "git commit " "Local repository ")
        (row "sync " "git pull && git push " "GitHub (cyberspace) ")
        (row "publish " "rsync " "Yoyodyne (www) "))
      (p "Note: sync is intentionally ambiguous—it also means lazy clustering sync (RFC-016). Context disambiguates. The ambiguity with git is preserved.[^d3]")
      (p "[^d3]: Design: Overloaded vocabulary reflects reality. \"Sync\" universally means bidirectional reconciliation. Fighting this creates cognitive load. Embrace it."))
    (subsection
      "Commit (Local)"
      (code bash "# Generate all formats\n./generate-rfcs.sh\n\n# Commit to vault\ngit add -A && git commit -m \"Regenerate RFC documentation\""))
    (subsection
      "Sync (GitHub)"
      (code bash "# Sync with remote\ngit pull && git push"))
    (subsection
      "Publish (Yoyodyne)"
      (code bash "# Publish to yoyodyne\nrsync -avz --chmod=D755,F644 \\\n  .html .ps *.txt \\\n  ddp@www.yoyodyne.com:/www/yoyodyne/ddp/cyberspace/")
      (p "Published URL: https://www.yoyodyne.com/ddp/cyberspace/")
      (p "Published: - .html - Web viewing - .ps - PostScript (archival, printing) - *.txt - Plain text - index.html - Catalog")
      (p "Permission model: - Directories: 755 (world-readable, owner-writable) - Files: 644 (world-readable, owner-writable)")))
  (section
    "Rich Formatting Pipeline"
    (subsection
      "HTML: Modern, Themeable"
      (p "HTML output uses rfc.css for rich presentation:")
      (p "- Light/dark themes: Respects prefers-color-scheme, toggleable - Typography: System fonts with monospace fallbacks for code - Code blocks: font-feature-settings ensures box-drawing alignment - Responsive: Mobile-friendly with print styles - Tables: Shadows, hover states, proper borders")
      (code css ":root {\n  --bg: #fafafa; --fg: #1a1a1a; --accent: #0066cc;\n}\n@media (prefers-color-scheme: dark) {\n  :root { --bg: #0d1117; --fg: #e6edf3; --accent: #58a6ff; }\n}"))
    (subsection
      "PostScript: Professional Typesetting"
      (p "PostScript uses groff with ms macros for rich output:")
      (p "- Markdown sources: pandoc → groff ms → PostScript - Text-only sources: enscript with fancy headers - Page layout: 1\" margins, 10pt body, Helvetica headers - Running headers: Title left, page number right")
      (code bash "# From markdown (via groff)\npandoc doc.md -t ms | groff -ms -Tps > doc.ps\n\n# From text (via enscript)\nenscript --fancy-header=enscript -p doc.ps doc.txt"))
    (subsection
      "Text: Immortal ASCII"
      (p "Plain text remains intentionally simple:")
      (p "- 78 columns for universal display - Unicode box-drawing converted to ASCII - No formatting dependencies - Grep-able, diff-able, eternal")))
  (section
    "Dependencies"
    (table
      (header "Tool " "Version " "Purpose ")
      (row "pandoc " "2.x+ " "Markdown → HTML, Markdown → groff ms ")
      (row "groff " "1.23+ " "ms macros → PostScript ")
      (row "enscript " "1.6+ " "Text → PostScript (fancy headers) ")
      (row "rsync " "3.x+ " "Publication "))
    (p "Install on macOS:")
    (code bash "brew install pandoc groff enscript")
    (p "PostScript viewers: TeXShop, Preview, Ghostscript, or read the source directly."))
  (section
    "Security Considerations"
    (subsection
      "Integrity"
      (p "Generated documents inherit integrity from: - Git version control - Vault signatures (releases)"))
    (subsection
      "Publication"
      (p "Remote publication uses: - SSH key authentication - No sensitive data in documents - World-readable permissions only")))
  (section
    "References"
    (p "1. Pandoc User's Guide (preserved) 2. PostScript Language Reference Manual - Adobe (preserved) 3. RFC-006: Vault System Architecture"))
  (section
    "Changelog"
    (p "- 2026-01-11 - Add rich formatting pipeline (groff, CSS themes) - 2026-01-07 - Add footnote categories, TOC, permuted index (KWIC) - 2026-01-07 - Replace PDF with PostScript (open format) - 2026-01-06 - Initial specification")))

