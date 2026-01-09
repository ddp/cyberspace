#!/bin/zsh
# RFC Documentation Pipeline
setopt null_glob
# Generates all RFC formats and index catalog
# Auto-discovers all rfc-*.md and rfc-*.txt files
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

# Discover RFCs from filesystem (unique basenames, sorted by number)
discover_rfcs() {
  for f in rfc-*.md rfc-*.txt; do
    [[ -f "$f" ]] && echo "${f%.*}"
  done | sort -u | sort -t- -k2,2n
}

# Check for duplicate RFC numbers
check_duplicates() {
  local prev_num=""
  local prev_rfc=""
  for rfc in "$@"; do
    local num=$(echo "$rfc" | sed 's/rfc-\([0-9]*\)-.*/\1/')
    if [[ -n "$prev_num" && "$num" == "$prev_num" ]]; then
      echo "WARNING: Duplicate RFC number $num:" >&2
      echo "  - $prev_rfc" >&2
      echo "  - $rfc" >&2
    fi
    prev_num="$num"
    prev_rfc="$rfc"
  done
}

# Build array from discovery
RFCS=("${(@f)$(discover_rfcs)}")

echo "Discovered ${#RFCS[@]} RFCs"
check_duplicates "${RFCS[@]}"

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

# Check if target is stale (missing or older than source)
is_stale() {
  local source="$1" target="$2"
  [[ ! -f "$target" ]] && return 0
  [[ "$source" -nt "$target" ]] && return 0
  return 1
}

# Generate HTML from markdown using pandoc
generate_html_from_md() {
  local base="$1"
  pandoc "${base}.md" -o "${base}.html" --standalone \
    --metadata title="" \
    --css="" \
    -V margin-top=2rem -V margin-bottom=2rem \
    2>/dev/null
}

# Generate HTML from plain text (pre-formatted, for .txt-only sources)
generate_html_from_txt() {
  local base="$1"
  local title=$(head -1 "${base}.txt")
  cat > "${base}.html" << EOF
<!DOCTYPE html>
<html><head><meta charset="UTF-8"><title>${title}</title>
<style>body{font-family:monospace;max-width:80ch;margin:2rem auto;padding:1rem;line-height:1.4;}
pre{white-space:pre-wrap;}</style>
</head><body><pre>$(sed 's/&/\&amp;/g; s/</\&lt;/g; s/>/\&gt;/g' "${base}.txt")</pre></body></html>
EOF
}

# Generate PostScript from text using enscript
generate_ps() {
  local base="$1" source="$2"
  enscript -B -f Courier10 -p "${base}.ps" "$source" 2>/dev/null
}

# Generate from Markdown source (prose, docs, RFCs)
generate_from_md() {
  local rfc="$1"
  local generated=""

  # Text: strip markdown to plain RFC-style text
  if is_stale "${rfc}.md" "${rfc}.txt"; then
    sed -e '/^```/d' \
        -e 's/^#\{1,6\} //' \
        -e 's/\*\*\([^*]*\)\*\*/\1/g' \
        -e 's/__\([^_]*\)__/\1/g' \
        -e 's/\*\([^*]*\)\*/\1/g' \
        -e 's/_\([^_]*\)_/\1/g' \
        -e 's/`\([^`]*\)`/\1/g' \
        -e 's/\[\([^]]*\)\]([^)]*)/\1/g' \
        -e 's/^---$/------------------------------------------------------------------------------/' \
        -e 's/^> /  /' \
        -e 's/[┌┐└┘├┤┬┴┼]/+/g' \
        -e 's/─/-/g' \
        -e 's/[│]/|/g' \
        -e 's/[▼]/v/g' \
        -e 's/[►]/>/g' \
        -e 's/[◄]/</g' \
        -e 's/[▲]/^/g' \
        "${rfc}.md" > "${rfc}.txt"
    generated="txt "
  fi

  # Hypertext: pandoc from markdown (proper HTML with markup)
  if is_stale "${rfc}.md" "${rfc}.html"; then
    generate_html_from_md "$rfc"
    generated="${generated}html "
  fi

  # PostScript: enscript from plain text
  if is_stale "${rfc}.txt" "${rfc}.ps"; then
    generate_ps "$rfc" "${rfc}.txt"
    generated="${generated}ps "
  fi

  if [[ -n "$generated" ]]; then
    echo "  ${rfc}: ${generated}"
  fi
}

# Generate from plain text source (IETF-style RFCs, no .md)
generate_from_txt() {
  local rfc="$1"
  local generated=""

  # Hypertext: wrap plain text in pre (no markdown to convert)
  if is_stale "${rfc}.txt" "${rfc}.html"; then
    generate_html_from_txt "$rfc"
    generated="${generated}html "
  fi

  # PostScript: enscript from text
  if is_stale "${rfc}.txt" "${rfc}.ps"; then
    generate_ps "$rfc" "${rfc}.txt"
    generated="${generated}ps "
  fi

  if [[ -n "$generated" ]]; then
    echo "  ${rfc}: ${generated}"
  fi
}

# Generate from LaTeX source (math, proofs, papers)
generate_from_tex() {
  local paper="$1"
  local generated=""

  # PostScript via LaTeX -> DVI -> PS
  if is_stale "${paper}.tex" "${paper}.ps"; then
    latex -interaction=nonstopmode "${paper}.tex" >/dev/null 2>&1
    latex -interaction=nonstopmode "${paper}.tex" >/dev/null 2>&1  # twice for refs
    if [[ -f "${paper}.dvi" ]]; then
      dvips -q -o "${paper}.ps" "${paper}.dvi" 2>/dev/null
      generated="ps "
    fi
    rm -f "${paper}.dvi" "${paper}.aux" "${paper}.log" "${paper}.out" 2>/dev/null
  fi

  # HTML (LaTeXML if available)
  if is_stale "${paper}.tex" "${paper}.html" && command -v latexmlc &>/dev/null; then
    latexmlc --dest="${paper}.html" "${paper}.tex" 2>/dev/null || true
    generated="${generated}html "
  fi

  if [[ -n "$generated" ]]; then
    echo "  ${paper}: ${generated}"
  fi
}

# Generate individual document formats (auto-detect source)
generate_formats() {
  local doc="$1"

  if [[ -f "${doc}.md" ]]; then
    generate_from_md "$doc"
  elif [[ -f "${doc}.txt" ]]; then
    generate_from_txt "$doc"
  elif [[ -f "${doc}.tex" ]]; then
    generate_from_tex "$doc"
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

# Publish to yoyodyne (world-readable web directory)
echo ""
echo "=== Publishing to yoyodyne ==="

YOYODYNE_HOST="ddp@www.yoyodyne.com"
YOYODYNE_PATH="~/cyberspace/spki/scheme/docs/rfc/"

if ssh -q -o BatchMode=yes -o ConnectTimeout=5 "$YOYODYNE_HOST" exit 2>/dev/null; then
  ssh "$YOYODYNE_HOST" "mkdir -p $YOYODYNE_PATH"
  rsync -av --delete *.html *.ps *.txt "$YOYODYNE_HOST:$YOYODYNE_PATH"
  echo "  ✓ Published to $YOYODYNE_HOST:$YOYODYNE_PATH"
else
  echo "  [skip] Cannot reach yoyodyne"
fi
