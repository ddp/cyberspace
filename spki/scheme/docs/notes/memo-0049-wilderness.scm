;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 49)
  (title "The Wilderness")
  (section
    "Abstract"
    (p "This Memo defines the Wilderness - the interstitial space between realms in Cyberspace. It establishes the cosmology of realms, wormholes, and affiliation."))
  (section
    "1. The Wilderness"
    (p "The Wilderness is the space between all realms. It is not empty - it is the medium through which all connections pass.")
    (code "┌─────────────────────────────────────────────────────────────────┐\n│                                                                 │\n│                      THE WILDERNESS                             │\n│                                                                 │\n│      ┌─────────┐              ┌─────────┐                      │\n│      │ Realm A │──wormhole───►│ Realm B │                      │\n│      └─────────┘              └─────────┘                      │\n│                                                                 │\n│                    ┌─────────┐                                  │\n│                    │ Realm C │                                  │\n│                    └─────────┘                                  │\n│                         ↑                                       │\n│                    (you are here)                               │\n│                    (unaffiliated)                               │\n│                                                                 │\n└─────────────────────────────────────────────────────────────────┘"))
  (section
    "2. States of Being"
    (subsection
      "2.1 Unaffiliated"
      (p "When you first enter Cyberspace, you are unaffiliated. You exist in the Wilderness with no realm to call home.")
      (code "You are unaffiliated, in the wilderness.")
      (p "This is the starting state. You have not: - Instantiated your own realm - Joined a confederation - Established any identity"))
    (subsection
      "2.2 Realm Instantiation"
      (p "To leave the Wilderness, you must instantiate a realm:")
      (code scheme "(create-realm 'myname)    ; create your own realm\n;; or\n(enroll-request 'myname)  ; join an existing confederation")
      (p "Once affiliated, you have a home:")
      (code "You entered the yoyodyne realm 5 minutes ago."))
    (subsection
      "2.3 Wormhole Transit"
      (p "Wormholes punch through the Wilderness to connect realms. When traversing a wormhole, you pass through the Wilderness - the same Wilderness where the unaffiliated wait.")
      (code "realm A ──► [wilderness] ──► realm B\n                 ↑\n            wormhole transit")))
  (section
    "3. Properties of the Wilderness"
    (subsection
      "3.1 Universality"
      (p "There is one Wilderness. All realms exist as islands within it. All wormholes traverse it."))
    (subsection
      "3.2 Neutrality"
      (p "The Wilderness belongs to no one. It has no authority, no governance, no federation. It simply is."))
    (subsection
      "3.3 Connectivity"
      (p "The Wilderness enables connection. Without it, realms would be isolated. Wormholes work because they have something to traverse.")))
  (section
    "4. The Wilderness of Mirrors"
    (p "A double-entendre:")
    (subsection
      "4.1 Angleton's Wilderness"
      (p "James Jesus Angleton, CIA counterintelligence chief, borrowed \"wilderness of mirrors\" from T.S. Eliot to describe the world of espionage. A place where:")
      (list
        (item "Reflexive control is dominant")
        (item "Nothing is as it seems")
        (item "Disinformation is the norm")
        (item "Trust is a vulnerability"))
      (p "In Cyberspace, the Wilderness acknowledges this reality:")
      (list
        (item "Trust is not given, it is established cryptographically")
        (item "Identity is not assumed, it is proven with keys")
        (item "Every claim requires verification")
        (item "The default stance is skepticism")))
    (subsection
      "4.2 The Tribal Wilderness"
      (p "The older meaning: outside civilization, unaffiliated with any tribe.")
      (list
        (item "No confederation claims you")
        (item "No federation protects you")
        (item "You belong to no one")
        (item "You are alone"))
      (p "Both meanings apply. The unaffiliated user is: - In a world where trust must be earned (Angleton) - Outside any group until they join one (tribal)")
      (p "The Wilderness is honest about both. You are alone. Trust nothing but your own crypto keys.")))
  (section
    "5. User Interface"
    (subsection
      "5.1 Status Line"
      (code "wilderness │ just now │ quiet")
      (p "When affiliated:")
      (code "yoyodyne │ 5 minutes │ replicating"))
    (subsection
      "5.2 Introspection"
      (code scheme "(self?)\n;; \"You are unaffiliated, in the wilderness.\"\n\n(federation?)\n;; \"You are not part of any confederation.\n;;  No peers discovered.\"")))
  (section
    "6. Design Rationale"
    (p "The Wilderness serves multiple purposes:")
    (p "1. Honest onboarding - Users know they are not yet part of anything 2. Unified metaphor - Same space for unaffiliated and wormhole transit 3. Security clarity - No implicit trust, no assumed identity 4. Poetic resonance - Evokes the uncertainty of the unaffiliated state"))
  (section
    "7. References"
    (p "1. Angleton, J.J. - \"Wilderness of Mirrors\" (intelligence terminology) 2. Eliot, T.S. - \"Gerontion\" (original source of the phrase) 3. Memo-010 - Federation Protocol 4. Memo-044 - Node Enrollment"))
  (section
    "Changelog"
    (list
      (item "2026-01-10")
      (item "Initial specification"))))

