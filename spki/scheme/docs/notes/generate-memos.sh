#!/bin/zsh
# Memo Documentation Pipeline (S-expression Edition)
setopt null_glob

# Always run from script's directory
cd "$(dirname "$0")"

# Memo namespace configuration
# Width may increase when namespace wraps (0000-9999 -> 00000-99999)
MEMO_NUMBER_WIDTH=4

# Format memo number with leading zeros
format_memo_num() {
  printf "%0${MEMO_NUMBER_WIDTH}d" "$1"
}

# Extract memo number from filename (preserves padding from filename)
extract_memo_num() {
  echo "$1" | sed 's/memo-\([0-9]*\)-.*/\1/'
}

# Generates all Memo formats and index catalog
# Auto-discovers all memo-*.scm source files
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

# Discover Memos from filesystem (unique basenames, sorted by number)
discover_memos() {
  for f in memo-*.scm; do
    [[ -f "$f" ]] || continue
    # Skip support files
    [[ "$f" == "memo-format.scm" ]] && continue
    echo "${f%.*}"
  done | sort -t- -k2,2n
}

# Check for duplicate Memo numbers
check_duplicates() {
  local prev_num=""
  local prev_memo=""
  for memo in "$@"; do
    local num=$(extract_memo_num "$memo")
    if [[ -n "$prev_num" && "$num" == "$prev_num" ]]; then
      echo "WARNING: Duplicate Memo number $num:" >&2
      echo "  - $prev_memo" >&2
      echo "  - $memo" >&2
    fi
    prev_num="$num"
    prev_memo="$memo"
  done
}

# Build array from discovery
MEMOS=("${(@f)$(discover_memos)}")

echo "Discovered ${#MEMOS[@]} Memos"
check_duplicates "${MEMOS[@]}"

# Check if memo is reserved/eluded
is_reserved() {
  local base="$1"
  [[ -f "${base}.scm" ]] && grep -q '(reserved)' "${base}.scm"
}

# Extract title from S-expression file
get_title() {
  local base="$1"
  if is_reserved "$base"; then
    echo "&lt;reserved&gt;"
  elif [[ -f "${base}.scm" ]]; then
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
  # Memos (skip reserved)
  for memo in "${MEMOS[@]}"; do
    is_reserved "$memo" && continue
    kwic_for_doc "$memo" "$(get_title "$memo")"
  done

  # README excluded from KWIC - it's not a Memo
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
  <title>Library of Cyberspace - Memos</title>
  <link rel="icon" id="favicon" href="data:image/svg+xml,<svg xmlns=%27http://www.w3.org/2000/svg%27 viewBox=%270 0 32 32%27><text x=%2716%27 y=%2725%27 font-family=%27serif%27 font-size=%2728%27 fill=%27%230f0%27 text-anchor=%27middle%27 font-weight=%27bold%27>λ</text></svg>">
  <link rel="stylesheet" href="index.css">
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
</head>
<body>
  <span class="theme-toggle" onclick="toggleTheme()" title="Toggle light/dark">[theme]</span>
  <h1>Library of Cyberspace - Memos</h1>
  <p>Request for Comments documents for the Library of Cyberspace preservation architecture.</p>

  <p>
    <a href="README.html">About the Library</a>
    [<a href="README.txt">txt</a>]
    [<a href="README.ps">ps</a>]
  </p>

  <h2>Memos</h2>
  <table>
    <thead>
      <tr>
        <th>Memo</th>
        <th>Title</th>
        <th>Formats</th>
      </tr>
    </thead>
    <tbody>
HEADER

  for memo in "${MEMOS[@]}"; do
    local title=$(get_title "$memo")
    local num=$(extract_memo_num "$memo")
    local formats
    if is_reserved "$memo"; then
      formats=""
    else
      formats='<a href="'"${memo}"'.txt">Text</a> <a href="'"${memo}"'.pdf">PDF</a> <a href="'"${memo}"'.html">Hypertext</a>'
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
  generate_kwic_entries | sort -t'|' -k1,1 -f | while IFS='|' read -r keyword left right memo; do
    local num=$(extract_memo_num "$memo")
    cat >> index.html << EOF
      <tr>
        <td class="left">${left}</td>
        <td class="keyword">${keyword}</td>
        <td class="right">${right}</td>
        <td class="memo"><a href="${memo}.html">${num}</a></td>
      </tr>
EOF
  done

  cat >> index.html << 'FOOTER'
    </tbody>
  </table>

  <footer>
    <p>Generated by the Library of Cyberspace.</p>
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

# Redundant words in titles - implied by project context
# Exception: memo-0000 "Declaration of Cyberspace" (founding document)
REDUNDANT_TITLE_WORDS="Cyberspace Cryptographic"

check_redundant_title() {
  local title="$1"
  local memo="$2"
  # Exception: Declaration of Cyberspace is the founding document
  [[ "$memo" == "memo-0000-declaration" ]] && return 0
  for word in ${=REDUNDANT_TITLE_WORDS}; do
    if [[ "$title" == *"$word"* ]]; then
      echo "  [WARN] $memo: '$word' is redundant in title"
      return 1
    fi
  done
  return 0
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

  # Check all Memo files exist (skip reserved/eluded)
  local missing=0
  local checked=0
  for memo in "${MEMOS[@]}"; do
    is_reserved "$memo" && continue
    checked=$((checked + 1))
    [[ ! -f "${memo}.html" ]] && missing=$((missing + 1))
  done

  if [[ $missing -gt 0 ]]; then
    echo "  [FAIL] $missing Memo HTML files missing"
    errors=$((errors + 1))
  else
    echo "  [OK] All $checked Memo HTML files present"
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

  # Check memo.css exists
  if [[ ! -f "memo.css" ]]; then
    echo "  [FAIL] memo.css missing"
    errors=$((errors + 1))
  else
    echo "  [OK] memo.css present"
  fi

  # Check for redundant words in titles
  local redundant=0
  for memo in "${MEMOS[@]}"; do
    is_reserved "$memo" && continue
    local title=$(get_title "$memo")
    check_redundant_title "$title" "$memo" || redundant=$((redundant + 1))
  done
  if [[ $redundant -gt 0 ]]; then
    echo "  [FAIL] $redundant memo(s) have redundant words in titles"
    errors=$((errors + 1))
  else
    echo "  [OK] No redundant title prefixes"
  fi

  # Check for stale "(planned)" markers that may have been implemented
  # This is a reminder - manual review required
  local planned_count
  planned_count=$(grep -l '(planned)' *.scm 2>/dev/null | wc -l | tr -d ' ')
  if [[ $planned_count -gt 0 ]]; then
    echo "  [INFO] $planned_count memo(s) contain '(planned)' markers - review for staleness:"
    grep -l '(planned)' *.scm 2>/dev/null | while read f; do
      echo "         - $f"
    done
    warnings=$((warnings + 1))
  fi

  # Remind to keep critical memos current
  # These define the system and must reflect implementation reality
  echo "  [REMIND] Critical memos must reflect current implementation:"
  echo "           - memo-0002-architecture.scm (system architecture)"
  echo "           - memo-0009-designer-notes.scm (design decisions, TCB, algorithms)"
  echo "           - memo-0043-cryptographic-entropy.scm (entropy requirements)"
  echo "           - memo-0045-security-architecture.scm (security model)"

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
echo "=== Memo Documentation Pipeline (S-expression) ==="
echo "Started: $(date -u '+%Y-%m-%d %H:%M:%SZ') ($(date '+%H:%M:%S %Z'))"
echo ""

# Extract kernel assertions (for Memo-046) - optional
if [[ -x ./extract-assertions.sh ]]; then
  echo "Extracting assertions..."
  ./extract-assertions.sh
fi

# Generate all formats via Scheme
echo ""
echo "Generating formats..."
csi -q generate-all.scm
GEN_STATUS=$?
if [[ $GEN_STATUS -ne 0 ]]; then
  echo "  [FAIL] Scheme generation failed with status $GEN_STATUS"
  exit 1
fi

# Compile LaTeX to PDF (if xelatex available)
# Disabled: too slow for routine generation. Run manually with: xelatex memo-*.tex
# MacTeX installs to /Library/TeX/texbin
[[ -d /Library/TeX/texbin ]] && export PATH="/Library/TeX/texbin:$PATH"
if false && command -v xelatex &> /dev/null; then
  echo ""
  echo "Compiling LaTeX to PDF..."
  PDF_COUNT=0
  PDF_FAIL=0
  for tex in memo-*.tex; do
    [[ ! -f "$tex" ]] && continue
    base="${tex%.tex}"
    pdf="${base}.pdf"
    # Only compile if tex is newer than pdf
    if [[ ! -f "$pdf" ]] || [[ "$tex" -nt "$pdf" ]]; then
      if xelatex -interaction=nonstopmode "$tex" > /dev/null 2>&1; then
        PDF_COUNT=$((PDF_COUNT + 1))
      else
        echo "  [FAIL] $tex"
        PDF_FAIL=$((PDF_FAIL + 1))
      fi
    fi
  done
  # Cleanup aux files
  rm -f memo-*.aux memo-*.log memo-*.out 2>/dev/null
  if [[ $PDF_COUNT -gt 0 ]]; then
    echo "  Compiled $PDF_COUNT PDFs"
  fi
  if [[ $PDF_FAIL -gt 0 ]]; then
    echo "  Failed: $PDF_FAIL"
  fi
else
  echo "  [SKIP] xelatex not found - PDF generation disabled"
fi

# Generate index
generate_index

echo ""
echo "Done."
echo "  HTML: $(ls memo-*.html 2>/dev/null | wc -l | tr -d ' ')"
echo "  PDF:  $(ls memo-*.pdf 2>/dev/null | wc -l | tr -d ' ')"
echo "  PS:   $(ls memo-*.ps 2>/dev/null | wc -l | tr -d ' ')"
echo "  TXT:  $(ls memo-*.txt 2>/dev/null | wc -l | tr -d ' ')"
echo "  TEX:  $(ls memo-*.tex 2>/dev/null | wc -l | tr -d ' ')"
echo "  SCM:  ${#MEMOS[@]}"

# Sanity check before publish
echo ""
sanity_check || exit 1

# Fix local permissions (your umask is 027, web needs 644)
chmod 644 *.html *.ps *.txt *.css 2>/dev/null || true

# Publish to yoyodyne
echo ""
echo "=== Publishing to yoyodyne ==="

YOYODYNE_HOST="ddp@www.yoyodyne.com"
YOYODYNE_BASE="/www/yoyodyne/ddp/cyberspace"
YOYODYNE_URL="https://www.yoyodyne.com/ddp/cyberspace/"
YOYODYNE_MEMO_PATH="$YOYODYNE_BASE/spki/scheme/docs/memo/"

if /usr/bin/ssh -q -o BatchMode=yes -o ConnectTimeout=5 "$YOYODYNE_HOST" exit 2>/dev/null; then
  /usr/bin/ssh "$YOYODYNE_HOST" "mkdir -p $YOYODYNE_MEMO_PATH"
  rsync -av --delete --chmod=F644,D755 *.html *.pdf *.ps *.txt *.css *.woff2 *.svg "$YOYODYNE_HOST:$YOYODYNE_MEMO_PATH"
  echo "  -> $YOYODYNE_MEMO_PATH"
  # Ensure web-readable permissions (rsync --chmod sometimes ignored by server umask)
  /usr/bin/ssh "$YOYODYNE_HOST" 'find '"$YOYODYNE_BASE"' -type f -exec chmod 644 {} \; && find '"$YOYODYNE_BASE"' -type d -exec chmod 755 {} \;'
  echo "  Published Memos to ${YOYODYNE_URL}spki/scheme/docs/memo/"
else
  echo "  [skip] Cannot reach yoyodyne"
fi

# Report elapsed time
END_TIME=$(date +%s)
ELAPSED=$((END_TIME - START_TIME))
echo ""
echo "Completed: $(date -u '+%Y-%m-%d %H:%M:%SZ') ($(date '+%H:%M:%S %Z')) [${ELAPSED}s]"
