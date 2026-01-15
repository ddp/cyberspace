;; Auto-converted from Markdown
;; Review and edit as needed

(memo
  (number 41)
  (title "IETF Normative Reference")
  (section
    "Abstract"
    (p "This document establishes the Internet Engineering Task Force (IETF) and its associated organizations as the normative model for Library of Cyberspace standards processes, document formats, and governance structures."))
  (section
    "Status of This Memo"
    (p "This document is an Informational RFC for the Library of Cyberspace community. It does not specify a protocol but establishes normative references to external standards bodies.")
    (p "Distribution of this memo is unlimited."))
  (section
    "Motivation"
    (p "The IETF has successfully governed Internet standards for over 35 years through open processes, rough consensus, and running code. We adopt their model not from lack of imagination but from recognition of what works.[^h1]")
    (p "[^h1]: Historical: The IETF emerged from the ARPANET community in 1986. Its processes evolved through practice, not theory. \"We reject kings, presidents, and voting. We believe in rough consensus and running code.\" — Dave Clark, 1992."))
  (section
    "Normative Organizations"
    (subsection
      "Internet Engineering Task Force (IETF)"
      (p "The principal standards body for Internet protocols.")
      (list
        (item "Website: https://www.ietf.org/")
        (item "Datatracker: https://datatracker.ietf.org/")
        (item "Mission: RFC 3935"))
      (p "The IETF operates through working groups organized by area. Participation is open to any individual. Standards emerge through rough consensus."))
    (subsection
      "Internet Architecture Board (IAB)"
      (p "Oversees the technical and engineering development of the Internet.")
      (list
        (item "Website: https://www.iab.org/")
        (item "Charter: RFC 2850"))
      (p "The IAB provides architectural oversight, adjudicates appeals, and appoints the RFC Series Editor."))
    (subsection
      "Internet Engineering Steering Group (IESG)"
      (p "Manages the IETF standards process and working groups.")
      (list
        (item "Responsibilities: RFC 2026, Section 6")
        (item "Appeals: RFC 2026, Section 6.5"))
      (p "The IESG reviews documents for publication as RFCs and manages the standards track progression."))
    (subsection
      "Internet Research Task Force (IRTF)"
      (p "Promotes research of importance to the evolution of the Internet.")
      (list
        (item "Website: https://irtf.org/")
        (item "Charter: RFC 2014"))
      (p "The IRTF focuses on longer-term research issues, complementing the IETF's near-term engineering focus."))
    (subsection
      "Internet Assigned Numbers Authority (IANA)"
      (p "Coordinates global Internet protocol parameters.")
      (list
        (item "Website: https://www.iana.org/")
        (item "Functions: RFC 5226"))
      (p "IANA maintains registries for protocol parameters, port numbers, and other Internet-wide identifiers."))
    (subsection
      "Internet Society (ISOC)"
      (p "Organizational home of the IETF, IAB, and IANA.")
      (list
        (item "Website: https://www.internetsociety.org/")
        (item "Charter: RFC 2031"))
      (p "ISOC provides legal and financial support for Internet standards development."))
    (subsection
      "Security Area Directorate (SECDIR)"
      (p "Reviews IETF documents for security issues.")
      (list
        (item "Area: Security (sec)")
        (item "Review: Mandatory for Standards Track documents"))
      (p "The Security Area ensures all specifications receive security review before publication. Security Considerations sections are required."))
    (subsection
      "IETF Working Groups"
      (p "Technical work happens in working groups organized by area.")
      (list
        (item "List: https://datatracker.ietf.org/wg/")
        (item "Process: RFC 2418"))
      (p "Table 1a: IETF Areas")
      (table
        (header "Area " "Focus ")
        (row "Applications and Real-Time (art) " "Application protocols ")
        (row "General (gen) " "Cross-area topics ")
        (row "Internet (int) " "IP and routing ")
        (row "Operations and Management (ops) " "Network operations ")
        (row "Routing (rtg) " "Routing protocols ")
        (row "Security (sec) " "Security protocols ")
        (row "Transport (tsv) " "Transport protocols ")
        (row "Web and Internet Transport (wit) " "HTTP, QUIC "))
      (p "Working groups are chartered, produce documents, and close when work is complete. Participation is open to all."))
    (subsection
      "RFC Editor"
      (p "Publishes and maintains the RFC series.")
      (list
        (item "Website: https://www.rfc-editor.org/")
        (item "Style Guide: RFC 7322")
        (item "Instructions: RFC 7997"))))
  (section
    "Normative RFCs"
    (p "The following IETF RFCs are normative for Library of Cyberspace processes:")
    (p "Table 1: Normative IETF RFCs")
    (table
      (header "RFC " "Title " "Relevance ")
      (row "RFC 2026 " "The Internet Standards Process, Revision 3 " "Standards track, categories, process ")
      (row "RFC 2119 " "Key Words for Use in RFCs " "MUST, SHOULD, MAY terminology ")
      (row "RFC 2223 " "Instructions to RFC Authors " "Document format, style ")
      (row "RFC 3935 " "A Mission Statement for the IETF " "Rough consensus, running code ")
      (row "RFC 5226 " "Guidelines for IANA Considerations " "Registry management ")
      (row "RFC 7322 " "RFC Style Guide " "Document formatting ")
      (row "RFC 7841 " "RFC Streams, Headers, and Boilerplates " "Document structure ")
      (row "RFC 8174 " "Ambiguity of Uppercase vs Lowercase in RFC 2119 " "Keyword clarification "))
    (subsection
      "RFC 2119 Keywords"
      (p "The key words \"MUST\", \"MUST NOT\", \"REQUIRED\", \"SHALL\", \"SHALL NOT\", \"SHOULD\", \"SHOULD NOT\", \"RECOMMENDED\", \"MAY\", and \"OPTIONAL\" in Library of Cyberspace documents are to be interpreted as described in RFC 2119 and RFC 8174.[^r1]")
      (p "[^r1]: Research: RFC 2119 keywords provide precise normative language. Implementations can be validated against MUST requirements. SHOULD indicates strong recommendation with documented exceptions.")))
  (section
    "Adopted Practices"
    (subsection
      "From IETF"
      (p "1. Rough Consensus — Decisions by general agreement, not voting 2. Running Code — Specifications validated by implementation 3. Open Participation — Anyone may contribute 4. Document-Driven — RFCs as primary record 5. Last Call — Review period before publication"))
    (subsection
      "From RFC Process"
      (p "1. Categories — Standards Track, Informational, Experimental, BCP, Historic 2. Status — Draft, Proposed, Implemented, Historic 3. Errata — Corrections without re-publication 4. Updates/Obsoletes — Document lifecycle management"))
    (subsection
      "From RFC Style"
      (p "1. ASCII-compatible — Plain text survives 2. Numbered sections — Unambiguous references 3. Security Considerations — Required section 4. IANA Considerations — Registry impact")))
  (section
    "Our Process"
    (p "The IETF process is thorough but obscure. We do our own thing.[^d1]")
    (p "[^d1]: Design: IETF processes evolved for Internet-scale coordination across thousands of participants. We're smaller, faster, more direct. We reference their norms, not their bureaucracy.")
    (p "What we take from IETF:")
    (list
      (item "RFC format — Document structure, numbering, required sections")
      (item "RFC 2119 keywords — MUST, SHOULD, MAY precision")
      (item "Security Considerations — Required in every specification")
      (item "Rough consensus — General agreement over voting")
      (item "Running code — Implementations validate specifications"))
    (p "What we skip:")
    (list
      (item "Working group charters")
      (item "Area director approval")
      (item "IESG review cycles")
      (item "Last call periods")
      (item "IANA registry formalism"))
    (p "Table 2: Our Process")
    (table
      (header "Step " "Action ")
      (row "1 " "Author drafts RFC ")
      (row "2 " "Submit to federation ")
      (row "3 " "Maintainer review ")
      (row "4 " "Rough consensus ")
      (row "5 " "Implement ")
      (row "6 " "Publish "))
    (p "Simple. Direct. We document, we build, we ship."))
  (section
    "Security Considerations"
    (p "This document establishes normative references and does not directly affect security. However, adherence to IETF security practices—including mandatory Security Considerations sections—strengthens the overall security posture of the Library."))
  (section
    "References"
    (subsection
      "Normative References"
      (p "1. RFC 2026 — Bradner, S., \"The Internet Standards Process\", BCP 9, 1996 2. RFC 2119 — Bradner, S., \"Key words for use in RFCs\", BCP 14, 1997 3. RFC 8174 — Leiba, B., \"Ambiguity of Uppercase vs Lowercase\", BCP 14, 2017"))
    (subsection
      "Informative References"
      (p "4. RFC 2014 — Weinrib, A., Postel, J., \"IRTF Research Group Guidelines\", 1996 5. RFC 2223 — Postel, J., Reynolds, J., \"Instructions to RFC Authors\", 1997 6. RFC 2850 — IAB, \"Charter of the Internet Architecture Board\", 2000 7. RFC 3935 — Alvestrand, H., \"A Mission Statement for the IETF\", 2004 8. RFC 5226 — Narten, T., Alvestrand, H., \"IANA Considerations\", 2008 9. RFC 7322 — Flanagan, H., Ginoza, S., \"RFC Style Guide\", 2014 10. RFC 7841 — Halpern, J., et al., \"RFC Streams, Headers, Boilerplates\", 2016")))
  (section
    "Acknowledgments"
    (p "The IETF community, whose 35+ years of open standards development provides the foundation we build upon. Rough consensus and running code."))
  (section
    "Changelog"
    (p "- 2026-01-07 — Initial specification")))

