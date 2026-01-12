;; Library of Cyberspace - RFC Directory
;; S-expression document format

(document
  (title "Library of Cyberspace")
  (subtitle "The Soup. The Realm. The Seal.")

  (section
    "What Is This?"
    (p "Imagine a library where:")
    (list
      (item "Your work is safe - because friends keep copies for each other")
      (item "Nothing gets lost - even if one computer fails")
      (item "You know who made what - like a signature on a painting")
      (item "It belongs to everyone - like a community garden"))
    (p "That's the Library of Cyberspace."))

  (section
    "Why Does This Matter?"
    (p "We all have things worth keeping: family photos, creative work, research, code, things we want to pass on.")
    (p "Right now, most of this lives on company servers. That works great... until the company shuts down, your account gets locked, or something just disappears.")
    (p "Friends don't disappear. Friends keep copies."))

  (section
    "The Simple Idea"
    (p "What if preserving things worked like borrowing books from friends?")
    (code "    You <----> Friend <----> Friend\n     |           |             |\n     +-----------+-------------+\n                 |\n      Everyone helps everyone.\n      Like a neighborhood library,\n      but for anything digital.")
    (p "That's really all this is."))

  (section
    "Our Promise to Each Other"
    (list
      (item "We keep copies - so nothing is lost")
      (item "We verify authenticity - so nothing is changed")
      (item "We share generously - because that's what friends do")
      (item "We help each other - because together we're stronger")))

  (section
    "A Newton for Cyberspace"
    (p "In 1993, Apple made something called the Newton. It had a revolutionary idea: your stuff just exists. You don't save files or open documents. Things float in a soup of objects, and you find them by asking questions.")
    (p "The Newton died because it needed a network that didn't exist yet. We have that network now.")
    (p "We're building the Newton it deserves: a soup that spans friends, objects that prove themselves, identity without permission, memory that can't be rewritten."))

  (section
    "RFC Purpose"
    (p "These Request for Comments documents serve as:")
    (list
      (item (term "Design Records") "Why decisions were made")
      (item (term "Implementation Specifications") "How features work")
      (item (term "Security Analysis") "Threat models and mitigations")
      (item (term "Future Reference") "Understanding the system later")))

  (section
    "Lineage"
    (p "Cyberspace stands on giants:")
    (table
      (header "System" "Era" "What We Learned")
      (row "VMS Clusters" "1983" "SET HOST - distributed presence")
      (row "Newton" "1993" "The soup - objects as medium, queries as navigation")
      (row "General Magic" "1994" "Agents that travel, carry intent, return with results")
      (row "SPKI/SDSI" "1996" "Capabilities, not identities")
      (row "AS/400" "1988" "Capability-based addressing")
      (row "Cambridge CAP" "1970s" "Hardware capabilities"))
    (p "Cyberspace is their synthesis: local-first realms, federated via capabilities, with agents swimming in the soup."))

  (section
    "Glossary"
    (table
      (header "Term" "Definition")
      (row "Realm" "A node's place in cyberspace - vault, principal, capabilities, objects. Local-first, sovereign.")
      (row "Vault" "The local content-addressed object store. The realm's storage.")
      (row "Principal" "A node's cryptographic identity (Ed25519 public key).")
      (row "Soup" "The queryable object space. A wilderness of mirrors.")
      (row "Seal" "Cryptographic binding - signing, archiving, committing. The primary verb.")))

  (footer
    (p "The Library of Alexandria burned. We can do better now.")
    (p "Not with a building, but with friendship. Not with guards, but with mathematics.")))
