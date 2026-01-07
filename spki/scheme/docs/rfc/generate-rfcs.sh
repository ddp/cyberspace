#!/bin/bash
# RFC Documentation Pipeline
# Generates all RFC formats and index catalog
#
# Source formats:
#   .md   - Markdown (prose, docs, RFCs) → pandoc
#   .tex  - LaTeX (math, proofs, papers) → pdflatex + latexmlc
#
# Output formats:
#   .html - Web viewing (standalone)
#   .pdf  - Archival, printing
#   .txt  - Plain text (IETF tradition, prose only)
#
# Computer science is math. Use the right tool for each.

set -e

RFCS=(
  rfc-000-declaration
  rfc-001-replication-layer
  rfc-002-architecture
  rfc-003-audit-trail
  rfc-004-spki-authorization
  rfc-005-metadata-levels
  rfc-006-vault-architecture
  rfc-007-threshold-governance
  rfc-008-shamir-sharing
  rfc-009-library-directory
  rfc-010-federation
  rfc-011-byzantine-consensus
  rfc-012-lamport-clocks
  rfc-013-tla-specification
  rfc-014-coq-extraction
  rfc-015-versioning-rollback
  rfc-016-lazy-clustering
  rfc-017-opera
  rfc-018-sealed-archive
  rfc-019-documentation-pipeline
)

# Extract title from markdown file
get_title_md() {
  head -1 "$1" | sed 's/^# //'
}

# Extract title from LaTeX file
get_title_tex() {
  grep -m1 '\\title{' "$1" 2>/dev/null | sed 's/.*\\title{\([^}]*\)}.*/\1/' || basename "$1" .tex
}

# Get title from any source
get_title() {
  local base="$1"
  if [[ -f "${base}.md" ]]; then
    get_title_md "${base}.md"
  elif [[ -f "${base}.tex" ]]; then
    get_title_tex "${base}.tex"
  else
    echo "$base"
  fi
}

# Generate from Markdown source (prose, docs, RFCs)
generate_from_md() {
  local rfc="$1"
  echo "Processing ${rfc} (markdown)..."

  # HTML (standalone)
  pandoc "${rfc}.md" -o "${rfc}.html" --standalone --metadata title="" 2>/dev/null

  # PDF (xelatex, IBM Plex Mono for code)
  pandoc "${rfc}.md" -o "${rfc}.pdf" --pdf-engine=xelatex -V monofont="IBM Plex Mono" 2>/dev/null

  # Plain text (78 columns, IETF style)
  pandoc "${rfc}.md" -o "${rfc}.txt" --to=plain --wrap=auto --columns=78 2>/dev/null

  echo "  -> .html .pdf .txt"
}

# Generate from LaTeX source (math, proofs, papers)
generate_from_tex() {
  local paper="$1"
  echo "Processing ${paper} (latex)..."

  # PDF (native LaTeX - what it was made for)
  pdflatex -interaction=nonstopmode "${paper}.tex" >/dev/null 2>&1
  pdflatex -interaction=nonstopmode "${paper}.tex" >/dev/null 2>&1  # twice for refs

  # HTML (LaTeXML - proper math rendering)
  if command -v latexmlc &>/dev/null; then
    latexmlc --dest="${paper}.html" "${paper}.tex" 2>/dev/null || true
    echo "  -> .pdf .html"
  else
    echo "  -> .pdf (latexmlc not installed, skipping HTML)"
  fi

  # Clean aux files
  rm -f "${paper}.aux" "${paper}.log" "${paper}.out" 2>/dev/null
}

# Generate individual document formats (auto-detect source)
generate_formats() {
  local doc="$1"

  if [[ -f "${doc}.md" ]]; then
    generate_from_md "$doc"
  elif [[ -f "${doc}.tex" ]]; then
    generate_from_tex "$doc"
  else
    echo "  [skip] ${doc} - no .md or .tex source"
  fi
}

# Generate index.html catalog
generate_index() {
  echo "Generating index.html..."

  cat > index.html << 'HEADER'
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Library of Cyberspace - RFC Index</title>
  <style>
    body {
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif;
      max-width: 900px;
      margin: 0 auto;
      padding: 2rem;
      line-height: 1.6;
      color: #333;
    }
    h1 { border-bottom: 2px solid #333; padding-bottom: 0.5rem; }
    table { width: 100%; border-collapse: collapse; margin: 1rem 0; }
    th, td { padding: 0.5rem; text-align: left; border-bottom: 1px solid #ddd; }
    th { background: #f5f5f5; }
    .formats a { margin-right: 0.5rem; font-size: 0.9rem; }
    .formats a:hover { text-decoration: underline; }
    footer { margin-top: 2rem; padding-top: 1rem; border-top: 1px solid #ddd; font-size: 0.9rem; color: #666; }
  </style>
</head>
<body>
  <h1>Library of Cyberspace - RFC Index</h1>
  <p>Request for Comments documents for the Library of Cyberspace preservation architecture.</p>

  <table>
    <thead>
      <tr>
        <th>RFC</th>
        <th>Title</th>
        <th>Formats</th>
      </tr>
    </thead>
    <tbody>
HEADER

  for rfc in "${RFCS[@]}"; do
    local title=$(get_title "$rfc")
    local num=$(echo "$rfc" | sed 's/rfc-0*//' | cut -d- -f1)
    local formats=""

    if [[ -f "${rfc}.md" ]]; then
      # Markdown source: html, pdf, txt, md
      formats='<a href="'"${rfc}"'.html">html</a> <a href="'"${rfc}"'.pdf">pdf</a> <a href="'"${rfc}"'.txt">txt</a> <a href="'"${rfc}"'.md">md</a>'
    elif [[ -f "${rfc}.tex" ]]; then
      # LaTeX source: html, pdf, tex (no txt - math doesn't work in plaintext)
      formats='<a href="'"${rfc}"'.html">html</a> <a href="'"${rfc}"'.pdf">pdf</a> <a href="'"${rfc}"'.tex">tex</a>'
    else
      continue
    fi

    cat >> index.html << EOF
      <tr>
        <td>${num}</td>
        <td>${title}</td>
        <td class="formats">${formats}</td>
      </tr>
EOF
  done

  cat >> index.html << 'FOOTER'
    </tbody>
  </table>

  <footer>
    <p>Generated by the Library of Cyberspace documentation pipeline.</p>
    <p>All formats are canonical and preserved in the Vault.</p>
  </footer>
</body>
</html>
FOOTER

  echo "  -> index.html"
}

# Main
echo "=== RFC Documentation Pipeline ==="
echo ""

for rfc in "${RFCS[@]}"; do
  generate_formats "$rfc"
done

generate_index

echo ""
echo "Done."
echo "  HTML: $(ls *.html 2>/dev/null | wc -l | tr -d ' ')"
echo "  PDF:  $(ls *.pdf 2>/dev/null | wc -l | tr -d ' ')"
echo "  TXT:  $(ls *.txt 2>/dev/null | wc -l | tr -d ' ')"
echo "  Sources:"
echo "    MD:  $(ls rfc-*.md 2>/dev/null | wc -l | tr -d ' ')"
echo "    TeX: $(ls rfc-*.tex 2>/dev/null | wc -l | tr -d ' ')"
