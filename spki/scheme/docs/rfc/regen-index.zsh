#!/bin/zsh
# Regenerate just the index.html without the full pipeline
setopt null_glob

discover_rfcs() {
  for f in rfc-*.scm; do
    [[ -f "$f" && "$f" != "rfc-format.scm" ]] && echo "${f%.scm}"
  done | sort -t- -k2,2n
}

RFCS=(${(@f)$(discover_rfcs)})
echo "Found ${#RFCS[@]} RFCs"

STOP_WORDS='a an and at for in of on or the to with'

is_stop_word() {
  local word=${(L)1}
  [[ " $STOP_WORDS " == *" $word "* ]]
}

get_title() {
  local base=$1
  if [[ -f "${base}.scm" ]]; then
    grep -o '(title "[^"]*")' "${base}.scm" | sed 's/(title "//; s/")//' | head -1
  else
    echo "$base"
  fi
}

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

generate_kwic_entries() {
  for rfc in "${RFCS[@]}"; do
    kwic_for_doc "$rfc" "$(get_title "$rfc")"
  done
}

# Generate index
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
      --bg: #000; --fg: #0f0; --fg-dim: #080; --fg-bright: #fff;
      --border: #0f0; --border-dim: #040; --bg-alt: #010;
      --link: #0f0; --link-visited: #0c0; --link-hover: #fff;
    }
    [data-theme="light"] {
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
  <span class="theme-toggle" onclick="toggleTheme()">◐ theme</span>
  <h1>Library of Cyberspace - RFC Index</h1>
  <p>Request for Comments documents for the Library of Cyberspace preservation architecture.</p>
  <p style="font-size: 8pt;">
    <a href="README.html">About the Library</a>
    [<a href="README.txt">txt</a>]
    [<a href="README.ps">ps</a>]
  </p>

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
  <table class="kwic">
    <tbody>
MIDDLE

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
      html.setAttribute('data-theme', current === 'light' ? 'dark' : 'light');
    }
  </script>
</body>
</html>
FOOTER

echo "  -> index.html"
