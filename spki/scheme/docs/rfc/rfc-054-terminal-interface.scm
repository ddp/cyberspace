;; Auto-converted from Markdown
;; Review and edit as needed

(rfc
  (number 54)
  (title "Terminal Interface Conventions")
  (section
    "Abstract"
    (p "The terminal is for operators. This RFC specifies visual conventions for the Cyberspace REPL: box drawing, tree displays, prompts, color usage, and output formatting. Consistency aids muscle memory."))
  (section
    "1. The Operator Interface"
    (p "The Cyberspace REPL is for hackers, admins, and operators—people who think in terms of data structures. This interface is deliberately different from the \"normie\" GUI interface (RFC-053).")
    (code "               CYBERSPACE\n                    |\n       +------------+------------+\n       |                         |\n  +----v-----+              +----v-----+\n  | Terminal |              | Friendly |\n  |   (cs)   | <- this RFC  |   Door   |\n  +----------+              +----------+"))
  (section
    "2. Box Drawing"
    (subsection
      "2.1 Unicode Box Characters"
      (p "Boxes use ASCII characters for web compatibility, Unicode in terminals:")
      (code "+  corner/tee/cross\n|  vertical line\n-  horizontal line")
      (p "Double-line boxes use = and # for emphasis:")
      (code "#  corner\n|  vertical\n=  horizontal"))
    (subsection
      "2.2 Box Construction Pattern"
      (p "Use closures to encapsulate box state:")
      (code scheme "(define (make-box title w)\n  \"Create a box drawing closure with given title and width\"\n  (let ((title-padded (string-append \" \" title \" \"))\n         (title-len (string-length title-padded))\n         (left-pad (quotient (- w title-len) 2))\n         (right-pad (- w title-len left-pad))\n         (header (string-append \"+\" (make-string left-pad #\\-)\n                               title-padded\n                               (make-string right-pad #\\-) \"+\\n\"))\n         (footer (string-append \"+\" (make-string w #\\-) \"+\\n\")))\n    (lambda (cmd . args)\n      (case cmd\n        ((header) header)\n        ((footer) footer)\n        ((line) (let ((content (if (null? args) \"\" (car args)))\n                       (pad (- w (string-length content) 2)))\n                  (string-append \"| \" content\n                                (make-string (max 0 pad) #\\space)\n                                \" |\\n\")))))))"))
    (subsection
      "2.3 Standard Box Widths"
      (table
        (header "Context " "Width " "Usage ")
        (row "Compact " "40 " "Small status displays ")
        (row "Standard " "50 " "Most dialogs ")
        (row "Wide " "65 " "Detailed information "))))
  (section
    "3. Tree Display"
    (subsection
      "3.1 Tree Characters"
      (code "+-  branch with more siblings\n+-  final branch (last item)\n|   vertical continuation"))
    (subsection
      "3.2 Tree Example"
      (code "hostname - up 3d 12:45:03\n+- 10 cores, 64GB, Apple M4\n+- 192.168.1.100 / 2001:db8::1...\n+- vault: .vault/ (keys) (audit)"))
    (subsection
      "3.3 Multi-level Trees"
      (code "vault (49 objects)\n+- archives (3)\n|  +- cyberspace-v0.59.tar.gz\n+- keys (2)\n|  +- starlight - Ed25519\n|  +- macmini - Ed25519\n+- releases (5)\n   +- v0.59 (signed)")))
  (section
    "4. Prompt"
    (subsection
      "4.1 Default Prompt"
      (p "The default prompt is a simple colon with trailing space:")
      (code ":")
      (p "This echoes the Newton's soup browser prompt."))
    (subsection
      "4.2 Prompt Variants"
      (table
        (header "Context " "Prompt " "Usage ")
        (row "Normal " ":  " "Default ")
        (row "Continuation " ">  " "Multi-line input ")
        (row "Debug " "[n]:  " "In debugger at frame n "))))
  (section
    "5. Color and Emphasis"
    (subsection
      "5.1 VT100 Codes"
      (p "Use ANSI/VT100 escape sequences sparingly:")
      (code scheme "(define vt100-bold    \"\\x1b[1m\")\n(define vt100-dim     \"\\x1b[2m\")\n(define vt100-normal  \"\\x1b[0m\")\n(define vt100-red     \"\\x1b[31m\")\n(define vt100-green   \"\\x1b[32m\")\n(define vt100-yellow  \"\\x1b[33m\")\n(define vt100-blue    \"\\x1b[34m\")"))
    (subsection
      "5.2 When to Use Color"
      (list
        (item "Green: Success, completion (✓)")
        (item "Red: Error, failure (✗)")
        (item "Yellow: Warning, attention needed")
        (item "Blue: Informational highlights")
        (item "Dim: Secondary information")
        (item "Bold: Headers, important values")))
    (subsection
      "5.3 Principle"
      (p "Color is enhancement, not information. All output MUST be readable without color (plain terminal, logging, piped output).")))
  (section
    "6. Status Symbols"
    (subsection
      "6.1 Checkmarks and Crosses"
      (code "[ok]  Success\n[!!]  Failure\n*     Bullet point\n->    Arrow, implies"))
    (subsection
      "6.2 Inline Separators"
      (p "For separating items in compact displays (session stats, status lines):")
      (code "-  dash separator\n|  pipe (more intrusive)\nv  down (bytes/data in)\n^  up (bytes/data out)")
      (p "Example session summary:")
      (code "Session: 4m 24s - 2 syncs - 3 seals - v1.2K ^856B"))
    (subsection
      "6.3 Sparklines"
      (p "For activity visualization over time, eight ASCII levels:")
      (code " ._,-~=+#")
      (p "Map to normalized data:")
      (code scheme "(define sparkline-chars '#(\" \" \".\" \"_\" \",\" \"-\" \"~\" \"=\" \"+\" \"#\"))"))))
  (section
    "7. Output Conventions"
    (subsection
      "7.1 Blank Lines"
      (list
        (item "One blank line before major output blocks")
        (item "One blank line after banner/header boxes")
        (item "No trailing blank lines in functions returning (void)")))
    (subsection
      "7.2 Indentation"
      (list
        (item "2 spaces for nested information - 4 spaces for code examples in help text")
        (item "Tree branches provide visual indentation")))
    (subsection
      "7.3 Truncation"
      (p "Long values should be truncated with ellipsis:")
      (code scheme "(define (short-id id)\n  \"Truncate id for display (max 16 chars)\"\n  (if (> (string-length id) 16)\n      (string-append (substring id 0 16) \"...\")\n      id))")))
  (section
    "8. Result Display"
    (subsection
      "8.1 History Variables"
      (code scheme "   ; last result\n1  ; second-to-last\n_2  ; third-to-last\n($n); result by number"))
    (subsection
      "8.2 Void"
      (p "Functions that print output typically return (void) to suppress duplicate display.")))
  (section
    "9. Messages"
    (subsection
      "9.1 Welcome Banner"
      (code "Cyberspace Scheme v0.59 (2026-01-11)\n  Starlight · Darwin-arm64 · 10 cores, 64GB, Apple M4\n  boot: 2026-01-11 22:30:45Z (14:30:45 PST)\n  IPv4: 192.168.1.100\n  IPv6: 2001:db8::1"))
    (subsection
      "9.2 Goodbye Message"
      (code "Returning to objective reality, Cyberspace frozen at 2026-01-11 22:35:22Z (14:35:22 PST).\n  Session: 4m 37s · 2 syncs · 47 objects · 2 keys"))
    (subsection
      "9.3 Timestamp Convention"
      (p "All timestamps in Cyberspace use ISO 8601 UTC format with Z suffix, followed by local time reference for operators:")
      (code "YYYY-MM-DD HH:MM:SSZ (HH:MM:SS TZ)")
      (p "UTC is canonical for storage, audit trails, and cross-node operations. The local time reference aids operators without affecting data integrity."))
    (subsection
      "9.4 Error Messages"
      (p "Errors should be clear and actionable:")
      (code "No signing key configured. Generate with (ed25519-keypair)")
      (p "Not:")
      (code "Error: nil key")))
  (section
    "10. Single-Character Shortcuts"
    (table
      (header "Symbol " "Function " "Description ")
      (row "\\" ".\\" " " "status " "Compact status display ")
      (row "\\" "?\\" " " "help " "Show help "))
    (p "These use pipe-delimited symbols to avoid conflict with Scheme."))
  (section
    "11. Terminal Window"
    (subsection
      "11.1 Title"
      (p "Set terminal title on startup:")
      (code scheme "(define (set-terminal-title title)\n  (display (string-append \"\\x1b]0;\" title \"\\x07\")))")
      (p "Format: <Hostname> Workstation"))
    (subsection
      "11.2 Clear Screen"
      (code scheme "(define (clear)\n  (display \"\\x1b[2J\\x1b[H\")\n  (void))")))
  (section
    "12. Implementation Notes"
    (subsection
      "12.1 UTF-8 and string-ref"
      (p "Do NOT use string-ref on strings containing multi-byte UTF-8 characters. Use vectors of strings instead:")
      (code scheme ";; WRONG - fails on multi-byte chars\n(string-ref \"▁▂▃\" idx)\n\n;; RIGHT - vector of strings\n(vector-ref '#(\"▁\" \"▂\" \"▃\") idx)"))
    (subsection
      "12.2 Width Calculations"
      (p "String length for box padding must account for display width, not byte length. ASCII characters are safe. For emoji or CJK, additional handling is needed.")))
  (section
    "13. Linting Checklist"
    (p "When auditing terminal output:")
    (p "1. [ ] Boxes use Unicode box-drawing characters 2. [ ] Trees use ├─ and └─ consistently 3. [ ] Prompt is :  (colon-space) 4. [ ] Colors are optional, not required for meaning 5. [ ] Error messages are actionable 6. [ ] Functions returning output use (void) 7. [ ] Long values are truncated with ... 8. [ ] Blank lines follow the convention 9. [ ] No ASCII art boxes (+---, |, etc.) 10. [ ] No tabs in output (spaces only)"))
  (section
    "14. References"
    (p "1. RFC-053 — The Normie Interface (GUI counterpart) 2. RFC-002 — Architecture (\"English on top, Scheme underneath\") 3. Unicode Standard — Box Drawing (U+2500–U+257F) 4. ECMA-48 — Control Functions for Coded Character Sets (VT100)"))
  (section
    "Changelog"
    (p "- 2026-01-11 — Initial specification")))

