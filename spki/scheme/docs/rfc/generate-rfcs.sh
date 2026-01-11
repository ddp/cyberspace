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
STOP_WORDS="a an and at for in of on or the to with"

is_stop_word() {
  local word=$(echo "$1" | tr '[:upper:]' '[:lower:]')
  for stop in ${=STOP_WORDS}; do
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
    # Clean punctuation that breaks word boundaries
    bare_title=$(echo "$bare_title" | sed 's/[()]//g; s/,//g')
    # zsh: use ${=var} for word splitting, arrays are 1-indexed
    local words=(${=bare_title})
    local num_words=${#words[@]}

    for ((i=1; i<=num_words; i++)); do
      local word="${words[$i]}"
      # Skip stop words
      is_stop_word "$word" && continue

      # Build left context (words before keyword)
      local left=""
      for ((j=1; j<i; j++)); do
        left="$left${words[$j]} "
      done

      # Build right context (words after keyword)
      local right=""
      for ((j=i+1; j<=num_words; j++)); do
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
<html lang="en" data-theme="dark">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Library of Cyberspace - RFC Index</title>
  <style>
    :root {
      /* Dark theme (default) - terminal phosphor */
      --bg: #000; --fg: #0f0; --fg-dim: #080; --fg-bright: #fff;
      --border: #0f0; --border-dim: #040; --bg-alt: #010;
      --link: #0f0; --link-visited: #0c0; --link-hover: #fff;
    }
    [data-theme="light"] {
      /* Light theme - parchment */
      --bg: #f4f1e8; --fg: #1a1a1a; --fg-dim: #555; --fg-bright: #000;
      --border: #1a1a1a; --border-dim: #ccc; --bg-alt: #e8e4d8;
      --link: #0645ad; --link-visited: #551a8b; --link-hover: #000;
    }
    @media (prefers-color-scheme: light) {
      :root:not([data-theme="dark"]) {
        --bg: #f4f1e8; --fg: #1a1a1a; --fg-dim: #555; --fg-bright: #000;
        --border: #1a1a1a; --border-dim: #ccc; --bg-alt: #e8e4d8;
        --link: #0645ad; --link-visited: #551a8b; --link-hover: #000;
      }
    }
    body {
      font-family: "SF Mono", Monaco, Inconsolata, "Fira Code", Consolas, monospace;
      max-width: 900px; margin: 0 auto; padding: 1rem;
      line-height: 1.25; background: var(--bg); color: var(--fg);
    }
    h1 { border-bottom: 1px solid var(--border); padding-bottom: 0.3rem; font-size: 14pt; margin: 0 0 0.5rem 0; }
    h2 { font-size: 11pt; margin: 1rem 0 0.3rem 0; border-bottom: 1px solid var(--border-dim); }
    p { margin: 0.3rem 0; font-size: 9pt; color: var(--fg-dim); }
    table { width: 100%; border-collapse: collapse; margin: 0.5rem 0; }
    th, td { padding: 0.2rem 0.4rem; text-align: left; border-bottom: 1px solid var(--border-dim); font-size: 9pt; }
    th { background: var(--bg-alt); color: var(--fg); }
    a { color: var(--link); text-decoration: none; }
    a:hover { color: var(--link-hover); text-decoration: underline; }
    a:visited { color: var(--link-visited); }
    .formats a { margin-right: 0.4rem; font-size: 8pt; }
    footer { margin-top: 1rem; padding-top: 0.5rem; border-top: 1px solid var(--border-dim); font-size: 8pt; color: var(--fg-dim); }
    .kwic { font-size: 8pt; }
    .kwic td { padding: 0.1rem 0.3rem; white-space: nowrap; }
    .kwic .left { text-align: right; color: var(--fg-dim); }
    .kwic .keyword { font-weight: bold; color: var(--fg); }
    .kwic .right { text-align: left; color: var(--fg-dim); }
    .kwic .rfc { text-align: left; }
    .theme-toggle { float: right; font-size: 8pt; cursor: pointer; color: var(--fg-dim); }
    .theme-toggle:hover { color: var(--fg); }
  </style>
</head>
<body>
  <span class="theme-toggle" onclick="toggleTheme()" title="Toggle light/dark">[theme]</span>
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
  <script>
    function toggleTheme() {
      const html = document.documentElement;
      const current = html.getAttribute('data-theme');
      const next = current === 'dark' ? 'light' : 'dark';
      html.setAttribute('data-theme', next);
      localStorage.setItem('theme', next);
    }
    // Load saved preference, or respect system, or default dark
    (function() {
      const saved = localStorage.getItem('theme');
      if (saved) {
        document.documentElement.setAttribute('data-theme', saved);
      } else if (window.matchMedia('(prefers-color-scheme: light)').matches) {
        document.documentElement.setAttribute('data-theme', 'light');
      }
    })();
  </script>
</body>
</html>
FOOTER

  echo "  -> index.html"
}

# Sanity check before publish
sanity_check() {
  local errors=0

  echo "=== Sanity Check ==="

  # Check KWIC has actual keywords (not empty)
  local kwic_entries
  kwic_entries=$(grep -c 'class="keyword">[^<]' index.html 2>/dev/null) || kwic_entries=0
  local empty_keywords
  empty_keywords=$(grep -c 'class="keyword"><' index.html 2>/dev/null) || empty_keywords=0

  if [[ $kwic_entries -lt 50 ]]; then
    echo "  [FAIL] KWIC index has only $kwic_entries entries (expected 50+)"
    errors=$((errors + 1))
  else
    echo "  [OK] KWIC index: $kwic_entries entries"
  fi

  if [[ $empty_keywords -gt 0 ]]; then
    echo "  [FAIL] KWIC has $empty_keywords empty keyword entries"
    errors=$((errors + 1))
  fi

  # Check all RFC files exist
  local missing=0
  for rfc in "${RFCS[@]}"; do
    [[ ! -f "${rfc}.html" ]] && missing=$((missing + 1))
  done

  if [[ $missing -gt 0 ]]; then
    echo "  [FAIL] $missing RFC HTML files missing"
    errors=$((errors + 1))
  else
    echo "  [OK] All ${#RFCS[@]} RFC HTML files present"
  fi

  # Check index.html is not tiny (corruption check)
  local index_size
  index_size=$(stat -f%z index.html 2>/dev/null) || index_size=$(stat -c%s index.html 2>/dev/null) || index_size=0
  if [[ $index_size -lt 10000 ]]; then
    echo "  [FAIL] index.html suspiciously small ($index_size bytes)"
    errors=$((errors + 1))
  else
    echo "  [OK] index.html size: $index_size bytes"
  fi

  if [[ $errors -gt 0 ]]; then
    echo ""
    echo "  $errors error(s) found - aborting publish"
    return 1
  fi

  echo "  All checks passed"
  return 0
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
        ((implemented++)) || true
      else
        ((pending++)) || true
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

# Sanity check before publish
echo ""
sanity_check || exit 1

# Publish to yoyodyne (world-readable web directory)
echo ""
echo "=== Publishing to yoyodyne ==="

YOYODYNE_HOST="ddp@www.yoyodyne.com"
YOYODYNE_BASE="/www/yoyodyne/ddp/cyberspace"
YOYODYNE_URL="https://www.yoyodyne.com/ddp/cyberspace/"

# RFC publish location only - don't overwrite main Library index
YOYODYNE_RFC_PATH="$YOYODYNE_BASE/spki/scheme/docs/rfc/"

if /usr/bin/ssh -q -o BatchMode=yes -o ConnectTimeout=5 "$YOYODYNE_HOST" exit 2>/dev/null; then
  /usr/bin/ssh "$YOYODYNE_HOST" "mkdir -p $YOYODYNE_RFC_PATH"
  rsync -av --delete --chmod=F644,D755 *.html *.ps *.txt "$YOYODYNE_HOST:$YOYODYNE_RFC_PATH"
  echo "  -> $YOYODYNE_RFC_PATH"
  # Ensure directories are world-readable for browser indexing
  /usr/bin/ssh "$YOYODYNE_HOST" 'find '"$YOYODYNE_BASE"' -type d -exec chmod 755 {} \;'
  echo "  Published RFCs to ${YOYODYNE_URL}spki/scheme/docs/rfc/"
else
  echo "  [skip] Cannot reach yoyodyne"
fi
