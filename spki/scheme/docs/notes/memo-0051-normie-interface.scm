;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 51)
  (title "The Normie Interface")
  (section
    "Abstract"
    (p "Cyberspace must be approachable by normal people. The terminal is for operators. This Memo specifies a friendly interface layer for everyone else."))
  (section
    "1. The Problem"
    (p "A normie asked: \"Why would I want to use this? I have Tahoe 26.2. They have recipes and cat pictures.\"")
    (p "Valid question. The answer must be compelling without mentioning: - Ed25519 - SPKI certificates - Hash chains - Merkle trees - S-expressions"))
  (section
    "2. What Normies Want"
    (code "What they have now:          What they actually want:\n────────────────────         ────────────────────────\niCloud                       My stuff, always there\nPhotos app                   My pictures, forever\nNotes                        My recipes, shareable\nMessages                     Talk to people I trust")
    (p "They don't want a distributed cryptographic vault. They want:")
    (p "1. My stuff is mine - Not rented from a corporation 2. It survives - No company shutdown deletes my photos 3. I control sharing - Family, not platforms 4. Privacy - My recipes aren't AI training data 5. Legacy - Grandkids can inherit the vault 6. No ads - I'm not the product"))
  (section
    "3. The Value Proposition"
    (code "┌─────────────────────────────────────────────────────────────────┐\n│                                                                 │\n│  A family vault, not a rental locker.                          │\n│                                                                 │\n│  Your photos. Your recipes. Your letters.                      │\n│  Shared with who you choose.                                   │\n│  Kept forever. Passed down.                                    │\n│                                                                 │\n│  No company in the middle.                                     │\n│  No terms of service.                                          │\n│  No sudden shutdowns.                                          │\n│                                                                 │\n│  Just you and the people you trust.                            │\n│                                                                 │\n└─────────────────────────────────────────────────────────────────┘"))
  (section
    "4. Two Doors"
    (code "                    CYBERSPACE\n                        │\n           ┌────────────┴────────────┐\n           │                         │\n      ┌────▼────┐              ┌─────▼─────┐\n      │ Terminal │              │  Friendly  │\n      │  (cs)    │              │    Door    │\n      └────┬────┘              └─────┬─────┘\n           │                         │\n      Operators                   Normies\n      Hackers                     Family\n      Admins                      Everyone")
    (subsection
      "4.1 The Terminal (Operators)"
      (code scheme ": (seal-commit \"vacation photos\")\n: (enroll-request 'mom)\n: (federation?)")
      (p "Full power. Full complexity. For those who want it."))
    (subsection
      "4.2 The Friendly Door (Normies)"
      (code "┌─────────────────────────────────────────┐\n│  Your Vault                    [+ Add]  │\n├─────────────────────────────────────────┤\n│  📷 Photos         1,234 items          │\n│  📝 Recipes          47 items           │\n│  📁 Documents       156 items           │\n├─────────────────────────────────────────┤\n│  Shared with: Mom, Dad, Sister          │\n│  [Invite someone]                       │\n└─────────────────────────────────────────┘")
      (p "Drag and drop. Click to share. No parens.")))
  (section
    "5. Interface Mapping"
    (table
      (header "Normie Action " "What Happens ")
      (row "Drag photo to vault " "(seal-commit \"photo.jpg\") ")
      (row "Click \"Invite Mom\" " "(enroll-request 'mom) ")
      (row "View shared items " "(soup 'shared) ")
      (row "Check who's online " "(federation?) ")
      (row "See vault contents " "(vault?) "))
    (p "The friendly door calls the same functions. Just no typing."))
  (section
    "6. Onboarding"
    (subsection
      "6.1 Terminal Onboarding"
      (code "You are unaffiliated, in the wilderness.\n\n: (self?)\nYou have no identity yet.\n  Use (enroll-request 'your-name) to join a confederation."))
    (subsection
      "6.2 Friendly Onboarding"
      (code "┌─────────────────────────────────────────┐\n│                                         │\n│  Welcome to your vault.                 │\n│                                         │\n│  What's your name?                      │\n│  [_]                      │\n│                                         │\n│  [Create my vault]                      │\n│                                         │\n│  ─────────────────────────────────────  │\n│  Already have a vault?                  │\n│  [Join family vault]                    │\n│                                         │\n└─────────────────────────────────────────┘")
      (p "Same operations. Different presentation.")))
  (section
    "7. Implementation Notes"
    (p "The friendly door could be:")
    (p "1. Native app - macOS, iOS, Android, Windows 2. Web interface - Local server, browser UI 3. Electron - Cross-platform (if we must) 4. Terminal TUI - Curses/ncurses for text lovers")
    (p "All doors lead to the same vault. All use the same Scheme underneath."))
  (section
    "8. Principles"
    (p "1. Never dumb down the core - Scheme stays Scheme 2. Add layers, don't subtract - Friendly is additional, not replacement 3. Same operations - Both doors do the same things 4. Gradual revelation - Normies can discover the terminal if curious 5. Family friendly - Grandma can use it"))
  (section
    "9. The Test"
    (p "If a normie can: - Create a vault in 30 seconds - Add a photo in 5 seconds - Invite family in 1 minute - Understand what they have")
    (p "Then we've succeeded."))
  (section
    "10. References"
    (p "1. Memo-0001 - Architecture (\"English on top, Scheme underneath\") 2. Memo-050 - The Wilderness (onboarding state)"))
  (section
    "Changelog"
    (list
      (item "2026-01-10")
      (item "Initial specification"))))

