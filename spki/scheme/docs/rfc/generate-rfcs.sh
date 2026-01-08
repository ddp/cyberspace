#!/bin/bash
# RFC Documentation Pipeline
# Generates all RFC formats and index catalog
#
# Source formats:
#   .md   - Markdown (prose, docs, RFCs) → pandoc
#   .tex  - LaTeX (math, proofs, papers) → latex + dvips
#
# Output formats:
#   .html - Web viewing (standalone)
#   .ps   - PostScript (archival, printing) - NeXT got it right
#   .txt  - Plain text (IETF tradition, prose only)
#
# PDF is Adobe's proprietary format dressed in ISO clothing.
# PostScript is open, stable, readable, and honest.

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
  rfc-020-content-addressed-storage
  rfc-021-capability-delegation
  rfc-022-key-ceremony
  rfc-023-agent-sandboxing
  rfc-024-network-protocol
  rfc-025-query-language
  rfc-026-garbage-collection
  rfc-027-vault-migration
  rfc-028-error-handling
  rfc-029-compression
  rfc-030-encryption-at-rest
  rfc-031-monitoring
  rfc-032-rate-limiting
  rfc-033-schema-evolution
  rfc-034-audit-protection
  rfc-035-mobile-agents
  rfc-036-quorum-voting
  rfc-037-node-roles
  rfc-038-local-inference
  rfc-039-ipv6-scaling
  rfc-040-security-architecture
  rfc-041-fuse-filesystem
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

  # PostScript via LaTeX -> DVI -> PS
  pandoc "${rfc}.md" -o "${rfc}.tex" --standalone \
    -V documentclass=article \
    -V classoption=oneside \
    -V geometry:margin=1in \
    2>/dev/null
  latex -interaction=nonstopmode "${rfc}.tex" >/dev/null 2>&1 || true
  latex -interaction=nonstopmode "${rfc}.tex" >/dev/null 2>&1 || true  # twice for refs
  if [[ -f "${rfc}.dvi" ]]; then
    dvips -q -o "${rfc}.ps" "${rfc}.dvi" 2>/dev/null
  fi
  # Clean intermediate files
  rm -f "${rfc}.tex" "${rfc}.dvi" "${rfc}.aux" "${rfc}.log" "${rfc}.out" "${rfc}.out.ps" 2>/dev/null

  # Plain text (78 columns, IETF style)
  pandoc "${rfc}.md" -o "${rfc}.txt" --to=plain --wrap=auto --columns=78 2>/dev/null

  echo "  -> .html .ps .txt"
}

# Generate from LaTeX source (math, proofs, papers)
generate_from_tex() {
  local paper="$1"
  echo "Processing ${paper} (latex)..."

  # PostScript via LaTeX -> DVI -> PS
  latex -interaction=nonstopmode "${paper}.tex" >/dev/null 2>&1
  latex -interaction=nonstopmode "${paper}.tex" >/dev/null 2>&1  # twice for refs
  if [[ -f "${paper}.dvi" ]]; then
    dvips -q -o "${paper}.ps" "${paper}.dvi" 2>/dev/null
  fi

  # HTML (LaTeXML - proper math rendering)
  if command -v latexmlc &>/dev/null; then
    latexmlc --dest="${paper}.html" "${paper}.tex" 2>/dev/null || true
    echo "  -> .ps .html"
  else
    echo "  -> .ps (latexmlc not installed, skipping HTML)"
  fi

  # Clean aux files
  rm -f "${paper}.dvi" "${paper}.aux" "${paper}.log" "${paper}.out" 2>/dev/null
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

# Stop words for KWIC index
STOP_WORDS="a an and for in of on or the to with"

is_stop_word() {
  local word=$(echo "$1" | tr '[:upper:]' '[:lower:]')
  for stop in $STOP_WORDS; do
    [[ "$word" == "$stop" ]] && return 0
  done
  return 1
}

# Generate KWIC permuted index entries
# Output: "keyword|left-context|right-context|rfc-name"
generate_kwic_entries() {
  for rfc in "${RFCS[@]}"; do
    local title=$(get_title "$rfc")
    # Strip "RFC-NNN: " prefix for rotation
    local bare_title=$(echo "$title" | sed 's/^RFC-[0-9]*: //')
    local words=($bare_title)
    local num_words=${#words[@]}

    for ((i=0; i<num_words; i++)); do
      local word="${words[$i]}"
      # Skip stop words
      is_stop_word "$word" && continue

      # Build left context (words before keyword)
      local left=""
      for ((j=0; j<i; j++)); do
        left="$left${words[$j]} "
      done

      # Build right context (words after keyword)
      local right=""
      for ((j=i+1; j<num_words; j++)); do
        right="$right ${words[$j]}"
      done

      echo "${word}|${left}|${right}|${rfc}"
    done
  done
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
    .kwic { font-family: monospace; font-size: 0.85rem; }
    .kwic td { padding: 0.25rem 0.5rem; white-space: nowrap; }
    .kwic .left { text-align: right; color: #666; }
    .kwic .keyword { font-weight: bold; }
    .kwic .right { text-align: left; color: #666; }
    .kwic .rfc { text-align: left; }
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
      # Text, PostScript, Hypertext Markup Language
      formats='<a href="'"${rfc}"'.txt">Text</a> <a href="'"${rfc}"'.ps">PostScript</a> <a href="'"${rfc}"'.html">Hypertext Markup Language</a>'
    elif [[ -f "${rfc}.tex" ]]; then
      # LaTeX source: PostScript, Hypertext Markup Language (no txt - math doesn't work in plaintext)
      formats='<a href="'"${rfc}"'.ps">PostScript</a> <a href="'"${rfc}"'.html">Hypertext Markup Language</a>'
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

  cat >> index.html << 'MIDDLE'
    </tbody>
  </table>

  <h2>Permuted Index (KWIC)</h2>
  <p>Key Word In Context index for discovery by concept.</p>
  <table class="kwic">
    <tbody>
MIDDLE

  # Generate and sort KWIC entries alphabetically by keyword
  generate_kwic_entries | sort -t'|' -k1,1 -f | while IFS='|' read -r keyword left right rfc; do
    local num=$(echo "$rfc" | sed 's/rfc-0*//' | cut -d- -f1)
    cat >> index.html << EOF
      <tr>
        <td class="left">${left}</td>
        <td class="keyword">${keyword}</td>
        <td class="right">${right}</td>
        <td class="rfc"><a href="${rfc}.html">${num}</a></td>
      </tr>
EOF
  done

  cat >> index.html << 'FOOTER'
    </tbody>
  </table>

  <footer>
    <p>Generated by the Library of Cyberspace documentation pipeline.</p>
    <p>Text: immortal. PostScript: open, stable, readable. Hypertext Markup Language: the dumb web.</p>
  </footer>
</body>
</html>
FOOTER

  echo "  -> index.html"
}

# Main
echo "=== RFC Documentation Pipeline ==="
echo ""

# Clean old PDFs
rm -f rfc-*.pdf 2>/dev/null

for rfc in "${RFCS[@]}"; do
  generate_formats "$rfc"
done

generate_index

echo ""
echo "Done."
echo "  HTML: $(ls *.html 2>/dev/null | wc -l | tr -d ' ')"
echo "  PS:   $(ls *.ps 2>/dev/null | wc -l | tr -d ' ')"
echo "  TXT:  $(ls *.txt 2>/dev/null | wc -l | tr -d ' ')"
echo "  Sources:"
echo "    MD:  $(ls rfc-*.md 2>/dev/null | wc -l | tr -d ' ')"
echo "    TeX: $(ls rfc-*.tex 2>/dev/null | wc -l | tr -d ' ')"

# RFC Implementation Coverage Check
echo ""
echo "=== RFC Implementation Coverage ==="

REPL_FILE="../../cyberspace-repl"
if [[ -f "$REPL_FILE" ]]; then
  # RFC keyword mappings (rfc-num:keyword)
  RFC_MAP="
003:audit-append
004:create-cert
006:seal-commit
010:federate
011:consensus
012:lamport
016:lazy-join
018:seal-archive
020:content-address
021:delegate
023:sandbox
025:query
035:tunnel
036:quorum
037:node-role
038:inference
041:vault-mount
"

  implemented=0
  pending=0
  pending_list=""

  for rfc in "${RFCS[@]}"; do
    # Extract RFC number (e.g., rfc-003-foo -> 003)
    num=$(echo "$rfc" | sed 's/rfc-\([0-9]*\)-.*/\1/')
    # Find keyword for this RFC
    keyword=$(echo "$RFC_MAP" | grep "^${num}:" | cut -d: -f2)

    if [[ -n "$keyword" ]]; then
      if grep -q "$keyword" "$REPL_FILE" 2>/dev/null; then
        ((implemented++))
      else
        ((pending++))
        pending_list="${pending_list}    - ${rfc} (${keyword})\n"
      fi
    fi
  done

  echo "  Implemented: $implemented"
  echo "  Pending:     $pending"

  if [[ $pending -gt 0 ]]; then
    echo ""
    echo "  Missing in REPL:"
    echo -e "$pending_list"
  fi
else
  echo "  [skip] REPL not found at $REPL_FILE"
fi
