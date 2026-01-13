#!/bin/zsh
# RFC Documentation Pipeline (S-expression Edition)
setopt null_glob
# Generates all RFC formats and index catalog
# Auto-discovers all rfc-*.scm source files
#
# Source format:
#   .scm  - S-expression documents (DSSSL-inspired)
#
# Output formats:
#   .html - Web viewing (standalone)
#   .ps   - PostScript (archival, printing) - NeXT got it right
#   .txt  - Plain text (IETF tradition)
#
# PDF is Adobe's proprietary format dressed in ISO clothing.
# PostScript is open, stable, readable, and honest.

set -e

# Discover RFCs from filesystem (unique basenames, sorted by number)
discover_rfcs() {
  for f in rfc-*.scm; do
    [[ -f "$f" ]] || continue
    # Skip support files
    [[ "$f" == "rfc-format.scm" ]] && continue
    echo "${f%.*}"
  done | sort -t- -k2,2n
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

# Extract title from S-expression file
get_title() {
  local base="$1"
  if [[ -f "${base}.scm" ]]; then
    # Extract (title "...") from S-expression
    grep -o '(title "[^"]*")' "${base}.scm" 2>/dev/null | sed 's/(title "//; s/")//' | head -1
  else
    echo "$base"
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

# Generate KWIC entry for a single document
kwic_for_doc() {
  local doc="$1"
  local title="$2"
  local bare_title=$(echo "$title" | sed 's/[()]//g; s/,//g')
  local words=(${=bare_title})
  local num_words=${#words[@]}

  for ((i=1; i<=num_words; i++)); do
    local word="${words[$i]}"
    is_stop_word "$word" && continue

    local left=""
    for ((j=1; j<i; j++)); do
      left="$left${words[$j]} "
    done

    local right=""
    for ((j=i+1; j<=num_words; j++)); do
      right="$right ${words[$j]}"
    done

    echo "${word}|${left}|${right}|${doc}"
  done
}

# Generate KWIC permuted index entries
# Output: "keyword|left-context|right-context|doc-name"
generate_kwic_entries() {
  # RFCs
  for rfc in "${RFCS[@]}"; do
    kwic_for_doc "$rfc" "$(get_title "$rfc")"
  done

  # README excluded from KWIC - it's not an RFC
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
  <link rel="icon" id="favicon" href="data:image/svg+xml,<svg xmlns=%27http://www.w3.org/2000/svg%27 viewBox=%270 0 32 32%27><text x=%2716%27 y=%2725%27 font-family=%27serif%27 font-size=%2728%27 fill=%27%230f0%27 text-anchor=%27middle%27 font-weight=%27bold%27>λ</text></svg>">
  <script>
(function(){
  var h=new Date().getHours(),c;
  if(h>=4&&h<6)c='%23845EC2';       // brahma muhurta - violet
  else if(h>=6&&h<8)c='%23ffd700';  // dawn - gold
  else if(h>=8&&h<11)c='%2300d4aa'; // morning - teal
  else if(h>=11&&h<14)c='%230f0';   // midday - phosphor
  else if(h>=14&&h<17)c='%2339ff14';// afternoon - neon
  else if(h>=17&&h<19)c='%23ff6600';// sunset - orange
  else if(h>=19&&h<22)c='%23ff3366';// evening - coral
  else c='%2300ffff';               // night - cyan
  document.getElementById('favicon').href='data:image/svg+xml,<svg xmlns=%27http://www.w3.org/2000/svg%27 viewBox=%270 0 32 32%27><text x=%2716%27 y=%2725%27 font-family=%27serif%27 font-size=%2728%27 fill=%27'+c+'%27 text-anchor=%27middle%27 font-weight=%27bold%27>λ</text></svg>';
})();
  </script>
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

  <p>
    <a href="README.html">About the Library</a>
    [<a href="README.txt">txt</a>]
    [<a href="README.ps">ps</a>]
  </p>

  <h2>RFCs</h2>
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
    local num=$(echo "$rfc" | sed 's/rfc-\([0-9]*\)-.*/\1/' | sed 's/^0*\([0-9]\)/\1/')
    local formats='<a href="'"${rfc}"'.txt">Text</a> <a href="'"${rfc}"'.ps">PostScript</a> <a href="'"${rfc}"'.html">Hypertext</a>'

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
    local num=$(echo "$rfc" | sed 's/rfc-\([0-9]*\)-.*/\1/' | sed 's/^0*\([0-9]\)/\1/')
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
    <p>S-expression source. Text: immortal. PostScript: open. Hypertext: accessible.</p>
  </footer>
  <script>
    function toggleTheme() {
      const html = document.documentElement;
      const current = html.getAttribute('data-theme');
      const next = current === 'dark' ? 'light' : 'dark';
      html.setAttribute('data-theme', next);
      localStorage.setItem('theme', next);
    }
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
  local warnings=0

  echo "=== Sanity Check ==="

  # Check KWIC has actual keywords
  local kwic_entries
  kwic_entries=$(grep -c 'class="keyword">[^<]' index.html 2>/dev/null) || kwic_entries=0

  if [[ $kwic_entries -lt 50 ]]; then
    echo "  [FAIL] KWIC index has only $kwic_entries entries (expected 50+)"
    errors=$((errors + 1))
  else
    echo "  [OK] KWIC index: $kwic_entries entries"
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

  # Check index.html is not tiny
  local index_size
  index_size=$(stat -f%z index.html 2>/dev/null) || index_size=$(stat -c%s index.html 2>/dev/null) || index_size=0
  if [[ $index_size -lt 10000 ]]; then
    echo "  [FAIL] index.html suspiciously small ($index_size bytes)"
    errors=$((errors + 1))
  else
    echo "  [OK] index.html size: $index_size bytes"
  fi

  # Check rfc.css exists
  if [[ ! -f "rfc.css" ]]; then
    echo "  [FAIL] rfc.css missing"
    errors=$((errors + 1))
  else
    echo "  [OK] rfc.css present"
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
START_TIME=$(date +%s)
echo "=== RFC Documentation Pipeline (S-expression) ==="
echo "Started: $(date -u '+%Y-%m-%d %H:%M:%SZ') ($(date '+%H:%M:%S %Z'))"
echo ""

# Extract kernel assertions (for RFC-046)
echo "Extracting assertions..."
./extract-assertions.sh

# Generate all formats via Scheme
echo ""
echo "Generating formats..."
csi -q generate-all.scm
GEN_STATUS=$?
if [[ $GEN_STATUS -ne 0 ]]; then
  echo "  [FAIL] Scheme generation failed with status $GEN_STATUS"
  exit 1
fi

# Generate index
generate_index

echo ""
echo "Done."
echo "  HTML: $(ls rfc-*.html 2>/dev/null | wc -l | tr -d ' ')"
echo "  PS:   $(ls rfc-*.ps 2>/dev/null | wc -l | tr -d ' ')"
echo "  TXT:  $(ls rfc-*.txt 2>/dev/null | wc -l | tr -d ' ')"
echo "  SCM:  ${#RFCS[@]}"

# Sanity check before publish
echo ""
sanity_check || exit 1

# Publish to yoyodyne
echo ""
echo "=== Publishing to yoyodyne ==="

YOYODYNE_HOST="ddp@www.yoyodyne.com"
YOYODYNE_BASE="/www/yoyodyne/ddp/cyberspace"
YOYODYNE_URL="https://www.yoyodyne.com/ddp/cyberspace/"
YOYODYNE_RFC_PATH="$YOYODYNE_BASE/spki/scheme/docs/rfc/"

if /usr/bin/ssh -q -o BatchMode=yes -o ConnectTimeout=5 "$YOYODYNE_HOST" exit 2>/dev/null; then
  /usr/bin/ssh "$YOYODYNE_HOST" "mkdir -p $YOYODYNE_RFC_PATH"
  rsync -av --delete --chmod=F644,D755 *.html *.ps *.txt *.css *.woff2 *.svg "$YOYODYNE_HOST:$YOYODYNE_RFC_PATH"
  echo "  -> $YOYODYNE_RFC_PATH"
  /usr/bin/ssh "$YOYODYNE_HOST" 'find '"$YOYODYNE_BASE"' -type d -exec chmod 755 {} \;'
  echo "  Published RFCs to ${YOYODYNE_URL}spki/scheme/docs/rfc/"
else
  echo "  [skip] Cannot reach yoyodyne"
fi

# Report elapsed time
END_TIME=$(date +%s)
ELAPSED=$((END_TIME - START_TIME))
echo ""
echo "Completed: $(date -u '+%Y-%m-%d %H:%M:%SZ') ($(date '+%H:%M:%S %Z')) [${ELAPSED}s]"
