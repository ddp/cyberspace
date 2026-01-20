;; Memo-0057: Typesetting
;; Absolving HTML's original sin

(memo
  (number 57)
  (title "Typesetting")
  (section
    "Abstract"
    (p "HTML was born without typographic discipline. Browsers render monospace text with variable-width box-drawing characters, destroying the careful geometry of ASCII diagrams. This memo specifies how Cyberspace solves the problem: convert character-cell art to SVG at generation time, preserving the author's intent in a form browsers cannot corrupt."))
  (section
    "The Original Sin"
    (p "In the beginning, there was the teletype. Characters occupied fixed cells. Box-drawing characters (│ ─ ┌ ┐ └ ┘) aligned perfectly because geometry was enforced by hardware.")
    (p "Then came HTML, and the browser vendors said: 'Let there be font substitution.' And there was chaos.")
    (p "The problem:")
    (list
      (item "Browsers substitute fonts freely, even within 'monospace'")
      (item "Box-drawing glyphs often come from different fonts than text")
      (item "Different fonts have different metrics")
      (item "A '│' from one font may be wider than '─' from another")
      (item "Vertical lines no longer align across rows"))
    (p "The result: carefully composed ASCII diagrams render as visual garbage. Decades of terminal art, protocol diagrams, and architectural sketches—broken by 'progress.'"))
  (section
    "The Solution: Compile to Geometry"
    (p "We solve this at the source. During memo generation, text containing box-drawing characters is converted to SVG—a format where geometry is explicit and browsers cannot reinterpret.")
    (subsection
      "Character Cell Model"
      (p "Every character occupies a fixed cell:")
      (code scheme "(define cell-width 10)    ; pixels\n(define cell-height 20)   ; pixels")
      (p "Text characters are positioned at cell centers. Box-drawing characters become geometric primitives—lines and rectangles with exact coordinates."))
    (subsection
      "Box-Drawing Primitives"
      (p "Each box-drawing codepoint maps to SVG elements:")
      (table
        (header "Glyph " "Codepoint " "SVG Primitives ")
        (row "─ " "U+2500 " "Horizontal line through cell center ")
        (row "│ " "U+2502 " "Vertical line through cell center ")
        (row "┌ " "U+250C " "Lines: center→right, center→down ")
        (row "┐ " "U+2510 " "Lines: center→left, center→down ")
        (row "└ " "U+2514 " "Lines: center→right, center→up ")
        (row "┘ " "U+2518 " "Lines: center→left, center→up ")
        (row "├ " "U+251C " "Lines: up↔down, center→right ")
        (row "┤ " "U+2524 " "Lines: up↔down, center→left ")
        (row "┬ " "U+252C " "Lines: left↔right, center→down ")
        (row "┴ " "U+2534 " "Lines: left↔right, center→up ")
        (row "┼ " "U+253C " "Lines: full cross "))
      (p "Double-line variants (═ ║ ╔ ╗ ╚ ╝) use the same geometry with doubled strokes."))
    (subsection
      "Text Grouping"
      (p "Consecutive text characters are grouped into single SVG text elements:")
      (code "Before: <text x=\"5\">c</text><text x=\"15\">h</text><text x=\"25\">a</text>...\nAfter:  <text x=\"0\">chaotic</text>")
      (p "This reduces SVG size and ensures proper kerning within text runs. Spaces and box-drawing characters break the grouping.")))
  (section
    "Auto-Alignment"
    (p "Authors make mistakes. Lines in a box diagram may differ by one character—an extra space, a missing padding. The renderer detects and corrects this automatically.")
    (subsection
      "The Algorithm"
      (list
        (item "Identify lines ending with box right-edges (│ ┐ ┘ ┤ ║ ╗ ╝)")
        (item "Find the most common width among these lines")
        (item "Adjust each box-edge line to match the target width")
        (item "Add spaces before the edge if too short")
        (item "Remove trailing spaces before the edge if too long"))
      (p "This preserves author intent while correcting typographic errors. A 64-character line among 63-character siblings gets trimmed. A 62-character line gets padded."))
    (subsection
      "Why Most Common, Not Maximum"
      (p "If 14 lines are 63 characters and 1 line is 64 characters, the outlier is the error. Taking the maximum would pad 14 correct lines to match 1 broken one. Taking the mode identifies the intended width.")))
  (section
    "Implementation"
    (p "The typesetting pipeline lives in memo-format.scm:")
    (code scheme ";; Core functions\n(utf8-chars str)           ; Extract Unicode codepoints\n(box-drawing-codepoint? cp) ; Identify box characters  \n(codepoint->svg cp cx cy)   ; Map to SVG primitives\n(fix-box-line-widths lines) ; Auto-align right edges\n(text->svg-diagram text)    ; Full conversion")
    (p "The pipeline:")
    (list
      (item "Split text into lines")
      (item "Auto-fix line widths for consistent box edges")
      (item "Process each character: box-drawing → geometry, text → grouped spans")
      (item "Emit SVG with embedded styles for theme compatibility")))
  (section
    "Design Principles"
    (list
      (item "Compile, don't interpret: Fix problems at generation time, not render time")
      (item "Preserve intent: The author's diagram should appear as conceived")
      (item "Fail gracefully: Unknown characters pass through as text")
      (item "Theme-aware: Use currentColor so diagrams respect dark/light mode")
      (item "Self-contained: Each SVG includes its own styles"))
    (p "These principles ensure diagrams render correctly across browsers, operating systems, and color schemes—now and in the future."))
  (section
    "Heritage"
    (p "This work stands on foundations:")
    (list
      (item "Knuth's TeX (1978): The discipline of precise typographic control")
      (item "Ossanna's troff (1973): Document formatting as compilation")
      (item "Adobe PostScript (1984): Page description as a programming language")
      (item "Unicode box-drawing block (1991): Standardized character geometry")
      (item "SVG 1.0 (2001): Vector graphics for the web"))
    (p "We honor these by taking typography seriously in an age that has largely forgotten it."))
  (section
    "References"
    (list
      (item "Knuth, D. E. (1984). The TeXbook")
      (item "Unicode Standard, Chapter 22: Symbols - Box Drawing")
      (item "SVG 1.1 Specification, W3C Recommendation")
      (item "Kernighan, B. W. (1978). A TROFF Tutorial")))
  (section
    "Changelog"
    (list
      (item "2026-01-20")
      (item "Initial specification"))))
