# RFC-042: IETF Normative Reference

**Status:** Implemented
**Category:** Informational
**Created:** 2026-01-07
**Author:** Library of Cyberspace Contributors

---

## Abstract

This document establishes the Internet Engineering Task Force (IETF) and its
associated organizations as the normative model for Library of Cyberspace
standards processes, document formats, and governance structures.

---

## Status of This Memo

This document is an Informational RFC for the Library of Cyberspace community.
It does not specify a protocol but establishes normative references to
external standards bodies.

Distribution of this memo is unlimited.

---

## Motivation

The IETF has successfully governed Internet standards for over 35 years through
open processes, rough consensus, and running code. We adopt their model not
from lack of imagination but from recognition of what works.[^h1]

[^h1]: Historical: The IETF emerged from the ARPANET community in 1986.
Its processes evolved through practice, not theory. "We reject kings,
presidents, and voting. We believe in rough consensus and running code."
— Dave Clark, 1992.

---

## Normative Organizations

### Internet Engineering Task Force (IETF)

The principal standards body for Internet protocols.

- **Website:** https://www.ietf.org/
- **Datatracker:** https://datatracker.ietf.org/
- **Mission:** RFC 3935

The IETF operates through working groups organized by area. Participation
is open to any individual. Standards emerge through rough consensus.

### Internet Architecture Board (IAB)

Oversees the technical and engineering development of the Internet.

- **Website:** https://www.iab.org/
- **Charter:** RFC 2850

The IAB provides architectural oversight, adjudicates appeals, and
appoints the RFC Series Editor.

### Internet Engineering Steering Group (IESG)

Manages the IETF standards process and working groups.

- **Responsibilities:** RFC 2026, Section 6
- **Appeals:** RFC 2026, Section 6.5

The IESG reviews documents for publication as RFCs and manages the
standards track progression.

### Internet Research Task Force (IRTF)

Promotes research of importance to the evolution of the Internet.

- **Website:** https://irtf.org/
- **Charter:** RFC 2014

The IRTF focuses on longer-term research issues, complementing the
IETF's near-term engineering focus.

### Internet Assigned Numbers Authority (IANA)

Coordinates global Internet protocol parameters.

- **Website:** https://www.iana.org/
- **Functions:** RFC 5226

IANA maintains registries for protocol parameters, port numbers,
and other Internet-wide identifiers.

### Internet Society (ISOC)

Organizational home of the IETF, IAB, and IANA.

- **Website:** https://www.internetsociety.org/
- **Charter:** RFC 2031

ISOC provides legal and financial support for Internet standards
development.

### RFC Editor

Publishes and maintains the RFC series.

- **Website:** https://www.rfc-editor.org/
- **Style Guide:** RFC 7322
- **Instructions:** RFC 7997

---

## Normative RFCs

The following IETF RFCs are normative for Library of Cyberspace processes:

*Table 1: Normative IETF RFCs*

| RFC | Title | Relevance |
|-----|-------|-----------|
| RFC 2026 | The Internet Standards Process, Revision 3 | Standards track, categories, process |
| RFC 2119 | Key Words for Use in RFCs | MUST, SHOULD, MAY terminology |
| RFC 2223 | Instructions to RFC Authors | Document format, style |
| RFC 3935 | A Mission Statement for the IETF | Rough consensus, running code |
| RFC 5226 | Guidelines for IANA Considerations | Registry management |
| RFC 7322 | RFC Style Guide | Document formatting |
| RFC 7841 | RFC Streams, Headers, and Boilerplates | Document structure |
| RFC 8174 | Ambiguity of Uppercase vs Lowercase in RFC 2119 | Keyword clarification |

### RFC 2119 Keywords

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
"SHOULD", "SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in
Library of Cyberspace documents are to be interpreted as described
in RFC 2119 and RFC 8174.[^r1]

[^r1]: Research: RFC 2119 keywords provide precise normative language.
Implementations can be validated against MUST requirements. SHOULD
indicates strong recommendation with documented exceptions.

---

## Adopted Practices

### From IETF

1. **Rough Consensus** — Decisions by general agreement, not voting
2. **Running Code** — Specifications validated by implementation
3. **Open Participation** — Anyone may contribute
4. **Document-Driven** — RFCs as primary record
5. **Last Call** — Review period before publication

### From RFC Process

1. **Categories** — Standards Track, Informational, Experimental, BCP, Historic
2. **Status** — Draft, Proposed, Implemented, Historic
3. **Errata** — Corrections without re-publication
4. **Updates/Obsoletes** — Document lifecycle management

### From RFC Style

1. **ASCII-compatible** — Plain text survives
2. **Numbered sections** — Unambiguous references
3. **Security Considerations** — Required section
4. **IANA Considerations** — Registry impact

---

## Divergences

The Library of Cyberspace diverges from IETF process in these areas:[^d1]

[^d1]: Design: We optimize for a smaller community with faster iteration.
IETF process overhead is justified at Internet scale; we adapt for
our context while preserving core principles.

*Table 2: Process Divergences*

| IETF Practice | Library Practice | Rationale |
|---------------|------------------|-----------|
| Working Groups | Direct contribution | Smaller community |
| Area Directors | Core maintainers | Flatter structure |
| IESG Review | Maintainer review | Faster iteration |
| RFC Editor | Automated pipeline | Self-publishing |
| IANA Registry | Vault namespace | Decentralized |

---

## Security Considerations

This document establishes normative references and does not directly
affect security. However, adherence to IETF security practices—including
mandatory Security Considerations sections—strengthens the overall
security posture of the Library.

---

## References

### Normative References

1. RFC 2026 — Bradner, S., "The Internet Standards Process", BCP 9, 1996
2. RFC 2119 — Bradner, S., "Key words for use in RFCs", BCP 14, 1997
3. RFC 8174 — Leiba, B., "Ambiguity of Uppercase vs Lowercase", BCP 14, 2017

### Informative References

4. RFC 2014 — Weinrib, A., Postel, J., "IRTF Research Group Guidelines", 1996
5. RFC 2223 — Postel, J., Reynolds, J., "Instructions to RFC Authors", 1997
6. RFC 2850 — IAB, "Charter of the Internet Architecture Board", 2000
7. RFC 3935 — Alvestrand, H., "A Mission Statement for the IETF", 2004
8. RFC 5226 — Narten, T., Alvestrand, H., "IANA Considerations", 2008
9. RFC 7322 — Flanagan, H., Ginoza, S., "RFC Style Guide", 2014
10. RFC 7841 — Halpern, J., et al., "RFC Streams, Headers, Boilerplates", 2016

---

## Acknowledgments

The IETF community, whose 35+ years of open standards development
provides the foundation we build upon. Rough consensus and running code.

---

## Changelog

- **2026-01-07** — Initial specification

---

**Implementation Status:** Implemented (normative reference established)
