# Cyberspace Designer Notes

## 2026-01-11: REPL UX Principles

### Output Philosophy

- **Silence is default** - Success prints nothing. Failure is an error.
- **No developer notes** - If it's not for the user, it doesn't print. No leaking implementation details.
- **Verbose is opt-in** - `--verbose` for play-by-play, otherwise quiet.
- **Consequential operations may announce** - Enrollment, federation changes, realm joins. But even these should maybe require `--verbose` because they're supposed to work.

### Async Model

- Prompts return frequently, don't block on long operations.
- Background work runs async, notify on completion.
- Notifications are optional - check when you want, never modal, never blocking.
- Your response is never required.

### Introspection by Semantic Type

- Not a generic notification queue.
- Organized by type of operation: enrollments, syncs, votes, federation requests.
- Each reflected where it makes sense in the REPL.
- Introspect by what it *is*, not dig through a queue.

### Governance

- Passive consent: silence is assent to federation consensus.
- If you don't vote, you live with the federation's decision.
- Fork your own security policy in your realm if you disagree.

### VMS Lessons

- $FAO-style formatted output for the TCB - clean ASCII.
- No calling the runtime from the TCB.
- The audit and protected subsystems live in their own UI layer.

### Help Command Behavior

`/?/` (and help variants) should always be useful across the REPL. When there's nothing contextual to offer, still try to be helpful - offer general guidance, suggest related commands, or at minimum apologize for not being able to offer specific help.

## 2026-01-13: TCSEC C2/B1 Heritage

### VMS Security Team

The Security Project Team was Derrell Piper, Mark Pilant, and Andy Goldstein.

The security subsystem was written exclusively in BLISS (with MACRO-32 fluency for reading the layers beneath). Now it's Scheme.

### VMS Security Services (System Services Reference)

Security-related services are grouped under a "Security services" family that includes $CHKPRO and a broader set of calls that manipulate identifiers, rights, and security profiles.

#### Security Services Family

Functional grouping covering services that operate on identifiers, rights lists, and security profiles, and that perform access decisions.

**Core access-check and audit path:**
- `$CHKPRO` - Check protection (manual access check)
- `$CHECK_ACCESS` - Check access (higher-level)
- `$AUDIT_EVENT` - Audit event
- `$AUDIT_EVENTW` - Audit event (wait)

**Rights database and identifiers:**
- `$ADD_IDENT` - Add identifier to rights database
- `$REMOVE_IDENT` - Remove identifier
- `$ADD_HOLDER` - Add holder to identifier
- `$REMOVE_HOLDER` - Remove holder from identifier
- `$ASCTOID` - Convert ASCII to identifier

#### User/Security Profile Services

Calls to build and use encoded profiles for CHKPRO and CHECK_ACCESS.

- `$CREATE_USER_PROFILE` - Build encoded user security profiles for use with $CHKPRO and $CHECK_ACCESS (via the usrpro argument)
- `$GETUAI` / `$SETUAI` - Get/set UAF fields and per-user security attributes

#### Privileges and Persona

**Privilege manipulation:**
- `$SETPRV` - Enable or disable privileges, affecting how CHKPRO and object protection fields are interpreted

**Persona handling:**
Later releases add `$PERSONA_*` services to let subsystems assume a requester's persona instead of re-implementing access checks - documented as the preferred alternative to manual CHKPRO-style logic.

### Relevance to RFC-032

The VMS security model - particularly the separation of access check ($CHKPRO) from profile creation ($CREATE_USER_PROFILE) and the later move to persona services - informs Cyberspace's approach to capability delegation and principal impersonation.

### 1.4 Lineage: System Service Vocabulary

The VMS system service vocabulary provides the conceptual heritage for Cyberspace's security primitives.

**Access Check Pattern:**
```
$CREATE_USER_PROFILE  →  builds encoded user security profile
        ↓
$CHKPRO / $CHECK_ACCESS  →  evaluates access using profile + object protection
        ↓
SS$_NORMAL / SS$_NOPRIV  →  grant or deny
```

**Key Item Codes (CHP$_*):**
| VMS | Cyberspace | Purpose |
|-----|------------|---------|
| CHP$_ACCESS | access-mask | Requested access type bitmask |
| CHP$_PROT | protection | SOGW protection mask |
| CHP$_OWNER | owner | Object owner identifier |
| CHP$_UIC | principal | Accessor's identity |
| CHP$_PRIV | privileges | Privilege mask |
| CHP$_ACL | acl | Access control list |
| CHP$_FLAGS | flags | Check options (observe/alter) |

**Flags (CHP$V_*):**
- `CHP$V_AUDIT` → `audit?` - Request access audit
- `CHP$V_OBSERVE` → `read?` - Read access
- `CHP$V_ALTER` → `write?` - Write access

**Return Status:**
| VMS | Cyberspace | Meaning |
|-----|------------|---------|
| SS$_NORMAL | #t | Access granted |
| SS$_NOPRIV | #f | Access denied |
| SS$_ACCVIO | 'accvio | Buffer access violation |
| SS$_IVACL | 'invalid-acl | Invalid ACL |

**Impersonation ($PERSONA_*):**
- `$PERSONA_CREATE` → `(impersonate principal)` - Assume another identity
- `$PERSONA_ASSUME` → `(with-persona p thunk)` - Execute as persona
- `$PERSONA_DELETE` → automatic GC - Release persona

Used by DECdfs and other distributed file services to act on behalf of remote clients without re-implementing access checks.

Sources: [VSI OpenVMS Wiki - $CHKPRO](https://wiki.vmssoftware.com/$CHKPRO), [VSI System Services Reference](https://vmssoftware.com/docs/VSI_SYS_SERVICES_REF_VOL_I.PDF)

## 2026-01-11: Bootstrap Display

Enhanced REPL startup to show:
- Host name, platform stamp (Darwin-arm64)
- Hardware summary (cores, RAM, chip)
- IPv4 and IPv6 addresses
- Vault/enrollment status

Fixed `plural` function for irregular plurals (identity -> identities).
Added IPv6 support to `introspect-network`.
