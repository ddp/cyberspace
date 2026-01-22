(memo
  (number 58)
  (title "Text Objects")
  (date "January 2026 (2026-01-20T00:00:00Z)")
  (section
    "Abstract"
    (p "Text in Cyberspace is not files. This Memo specifies the native text object representation: gap buffers for editing, merkle chunks for storage, and how editors like Electric Pencil, TECO, and Schemacs share a common substrate."))
  (section
    "The Problem with Files"
    (p "Unix thinks text lives in files. Files are byte streams with names. You open them, read them into memory, edit the memory, write them back. The file is the truth; memory is a copy.")
    (p "This is backwards. In Cyberspace, the text IS the object. It lives in the soup, content-addressed. There is no 'file' to open—there is only the text, and operations on it. Editors are views, not owners."))
  (section
    "Text as Object"
    (p "A text object has:")
    (list
      (item "Content: the characters")
      (item "Cursor: current position (for editing)")
      (item "Hash: content address in the soup")
      (item "Modified: dirty bit for seal semantics"))
    (p "Text objects are created, edited, and sealed. Once sealed, they are immutable—editing creates a new object with a new hash. The soup naturally preserves history."))
  (section
    "Gap Buffer: The Editing Representation"
    (p "For editing, text uses a gap buffer—the same data structure Emacs has used for 50 years. A gap buffer is an array with a gap at the cursor position:")
    (code "[text before cursor][    gap    ][text after cursor]")
    (p "Operations:")
    (table
      (header "Operation" "Cost" "Mechanism")
      (row "Insert at cursor" "O(1)" "Fill gap from left")
      (row "Delete at cursor" "O(1)" "Expand gap")
      (row "Move cursor" "O(n)" "Shift text across gap")
      (row "Random access" "O(1)" "Index arithmetic"))
    (p "The gap buffer is mutable. It is the working copy during editing. When you seal, the gap is closed and the content is hashed."))
  (section
    "Merkle Chunks: The Storage Representation"
    (p "For storage in the soup, large text objects are chunked into a merkle tree:")
    (code scheme "(text-object
  (chunks
    sha512:abc123...  ; first 64KB
    sha512:def456...  ; second 64KB
    sha512:789ghi...  ; third 64KB
  )
  (root sha512:xyz789...))")
    (p "Small edits touch one chunk, creating one new hash. The rest of the tree stays the same. This scales to 2^128 addressable objects without copying gigabytes on every keystroke."))
  (section
    "Seal Semantics"
    (p "Text follows the chaotic/quiescent state model (Memo-010):")
    (list
      (item "Chaotic: text is being edited, gap buffer is mutable")
      (item "Quiescent: text is sealed, content-addressed, immutable"))
    (p "Sealing a text object:")
    (code scheme "(define hash (text-seal t))  ; returns content address")
    (p "Unsealing retrieves a copy for editing:")
    (code scheme "(define t (text-unseal hash))  ; new gap buffer, same content")
    (p "Every sealed version persists. Undo is just pointing to the previous hash. Branching is natural—two editors can seal independently from the same starting point."))
  (section
    "Editors as Views"
    (p "Electric Pencil, TECO, and Schemacs all use the same text object. They differ in interface, not representation:")
    (table
      (header "Editor" "Heritage" "Interface" "Style")
      (row "Electric Pencil" "Shrayer 1976" "Full-screen ANSI" "Visual, WYSIWYG")
      (row "TECO" "Murphy 1962" "Command-line" "Programmatic, macros")
      (row "Schemacs" "Cyberspace 2026" "Full-screen ANSI" "Emacs keybindings"))
    (p "All three import the text module. All operate on gap buffers. All seal to the soup. The buffer is the truth; editors are lenses.")
    (p "Schemacs provides Emacs muscle memory—C-f, C-b, C-n, C-p, C-a, C-e, C-k, C-y—without the weight of elisp or decades of accumulated configuration. For those whose fingers speak Emacs, Schemacs is home."))
  (section
    "API Summary"
    (subsection
      "Construction"
      (code scheme "(text-new)              ; empty text
(text-from-string s)    ; from string
(text-from-file path)   ; load file (for bootstrap)"))
    (subsection
      "Query"
      (code scheme "(text-length t)         ; character count
(text-cursor t)         ; cursor position
(text-char-at t pos)    ; character at position
(text->string t)        ; extract as string
(text-modified? t)      ; dirty bit"))
    (subsection
      "Movement"
      (code scheme "(text-goto! t pos)      ; absolute position
(text-move! t delta)    ; relative movement
(text-beginning! t)     ; start of text
(text-end! t)           ; end of text
(text-line-start! t)    ; start of line
(text-line-end! t)      ; end of line"))
    (subsection
      "Editing"
      (code scheme "(text-insert! t str)    ; insert at cursor
(text-delete! t n)      ; delete n chars forward
(text-kill-line! t)     ; delete to end of line
(text-replace! t s e new) ; replace region"))
    (subsection
      "Search"
      (code scheme "(text-search t pattern) ; find forward, return position or #f
(text-search-backward t pattern)"))
    (subsection
      "Soup"
      (code scheme "(text-seal t)           ; seal to soup, return hash
(text-unseal hash)      ; load from soup
(text-hash t)           ; content address")))
  (section
    "Implementation Notes"
    (p "The gap buffer implementation is in text.scm. Key decisions:")
    (list
      (item "Vector of characters, not string (for mutation)")
      (item "Automatic growth when gap fills (doubling)")
      (item "Gap size defaults to 256 characters")
      (item "Line operations scan for newlines (no line table yet)"))
    (p "Future optimizations:")
    (list
      (item "Rope overlay for very large texts")
      (item "Line index for O(1) line access")
      (item "Piece table variant for collaborative editing")
      (item "Lazy chunk loading for huge objects")))
  (section
    "See Also"
    (references
      (ref "Memo-0022" "2026" "Content-Addressed Storage")
      (ref "Memo-0051" "2026" "Terminal Interface Conventions")
      (ref "text.scm" "2026" "Implementation")
      (ref "pencil.scm" "2026" "Electric Pencil editor")
      (ref "teco.scm" "2026" "TECO editor")
      (ref "schemacs.scm" "2026" "Schemacs editor"))))
