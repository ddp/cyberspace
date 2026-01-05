# DECset: Digital's Integrated Software Engineering Environment

This collection contains documentation for DECset, Digital Equipment Corporation's layered product suite for software development on OpenVMS systems.

## What is DECset?

**DECset** = Digital Equipment Corporation Software Engineering Toolset

**Purpose:**
An integrated CASE (Computer-Aided Software Engineering) environment providing tools for the complete software development lifecycle on OpenVMS (VAX and Alpha).

**Philosophy:**
> "NAVIGATE-EDIT-COMPILE-DEBUG cycle integration"

All tools work together seamlessly, sharing data through common repositories (CDD, SCA database).

## The DECset Components

**Core Products:**
1. **LSE** (Language-Sensitive Editor) - Context-aware source editor
2. **SCA** (Source Code Analyzer) - Cross-reference and analysis
3. **CMS** (Code Management System) - Version control
4. **MMS** (Module Management System) - Build automation (like make)
5. **PCA** (Performance and Coverage Analyzer) - Profiling and testing
6. **DTM** (DEC Test Manager) - Automated testing framework

**Supporting Infrastructure:**
- **CDD/Repository** (Common Data Dictionary) - Centralized metadata
- **LSE Templates** - Language-specific editing patterns
- **Callable routines** - Programmatic access to tools

## The Documentation

### decset-spd.pdf
**VSI DECset for OpenVMS Software Product Description**
- Official product overview
- Component descriptions
- System requirements
- Ordering information

**Product Suite Contents:**

**Language-Sensitive Editor (LSE):**
- Context-aware editing
- Syntax-directed templates
- Language-specific knowledge
- Integrated with debugger and SCA

**Source Code Analyzer (SCA):**
- Cross-reference database
- "Where is this function called?"
- "Show me all uses of this variable"
- Call graphs and dependency analysis

**Code Management System (CMS):**
- Version control (like RCS, SCCS)
- Element libraries
- Generation tracking
- Merge support

**Module Management System (MMS):**
- Dependency-based builds
- Like Unix `make` but integrated with CDD
- Automatic dependency detection
- Parallel builds

**Performance and Coverage Analyzer (PCA):**
- Execution profiling
- Code coverage analysis
- "Which functions are hotspots?"
- "What code wasn't tested?"

**DEC Test Manager (DTM):**
- Test harness framework
- Regression testing
- Test result tracking
- Integration with CMS

**Supported Languages:**
- Ada
- BASIC
- BLISS
- C
- C++
- COBOL
- FORTRAN
- Pascal
- PL/I

### decset-lse-sca-reference.pdf
**VSI DECset Language-Sensitive Editor / Source Code Analyzer Reference Manual**
- Comprehensive command reference
- LSE and SCA integration
- Database management
- Callable routines

**LSE Features:**

**1. Language-Aware Editing:**
```
Command: EXPAND IF
Result (in C):
    if () {

    }
    [Cursor positioned in condition]
```

**2. Token Navigation:**
- `NEXT WORD`, `PREVIOUS WORD` - Move by language tokens
- `NEXT PLACEHOLDER` - Jump to next template fill-in
- `GOTO DECLARATION` - Jump to variable/function definition

**3. Syntax Checking:**
- Real-time syntax validation
- Compile without leaving editor
- Jump to error locations

**4. Customization:**
- User-defined templates
- Custom key bindings
- Language extensions

**SCA Features:**

**1. Query Types:**
- `FIND SYMBOL` - Locate definitions
- `FIND ALL REFERENCES` - Find all uses
- `SHOW CALL_TREE` - Display call hierarchy
- `SHOW USED_BY` - What calls this function?

**2. Database Operations:**
```
$ SCA LOAD module.ana           ! Load analysis data
$ SCA FIND FUNCTION sqrt        ! Find sqrt function
$ SCA SHOW CALLS sqrt           ! What does sqrt call?
$ SCA SHOW CALLED_BY sqrt       ! What calls sqrt?
```

**3. Code Metrics:**
- Lines of code
- Cyclomatic complexity
- Module dependencies
- Dead code detection

**4. Cross-Language Analysis:**
- Track calls across Ada, C, FORTRAN
- Mixed-language application analysis
- Interface verification

### decset-program-design-guide.pdf
**VSI DECset Guide to Detailed Program Design**
- Methodology guide
- Best practices
- Integration workflows
- Example use cases

**The Integrated Development Cycle:**

**1. DESIGN Phase:**
- Create CDD entries for data structures
- Define module interfaces
- Set up MMS description files

**2. EDIT Phase (LSE):**
- Navigate to module with `GOTO DECLARATION`
- Use templates for consistency
- LSE enforces coding standards

**3. ANALYZE Phase (SCA):**
- Build SCA database
- Check for unused variables
- Verify interface consistency
- Generate call graphs

**4. BUILD Phase (MMS):**
- `MMS` rebuilds only changed modules
- Parallel compilation
- Automatic dependency tracking

**5. TEST Phase (DTM + PCA):**
- Run test suite with DTM
- Measure coverage with PCA
- Profile performance bottlenecks
- Regression testing

**6. DEBUG Phase:**
- OpenVMS Debugger integrated with LSE
- Source-level debugging
- Conditional breakpoints
- Call stack inspection

**7. VERSION CONTROL (CMS):**
- Check out module for editing
- Track changes with annotations
- Merge concurrent edits
- Tag releases

**Workflow Example:**
```
$ LSE                           ! Edit source
  LSE> GOTO BUFFER my_module.c
  LSE> [edit code]
  LSE> COMPILE/ANALYSIS         ! Generate .ANA file
  LSE> EXIT

$ SCA LOAD my_module.ana        ! Load into SCA database

$ SCA FIND FUNCTION calculate   ! Find function
$ SCA SHOW CALLS calculate      ! See what it calls

$ MMS                           ! Rebuild project
  [MMS rebuilds only changed files]

$ PCA RUN my_program            ! Profile execution
$ PCA SHOW COVERAGE             ! Check test coverage
```

### decset-lse-cli-reference.pdf
**Language-Sensitive Editor Command-Line Interface and Callable Routines Reference**
- Complete LSE command reference
- Scripting LSE operations
- Callable routine API

**LSE Callable Routines:**

**Why Callable Routines?**
- Automate editor operations
- Integrate LSE into custom tools
- Build specialized development environments

**Example (from DCL script):**
```
$ CALL LSE$INITIALIZE
$ CALL LSE$LOAD_BUFFER("module.c")
$ CALL LSE$COMPILE
$ CALL LSE$QUIT
```

**Programmatic Access:**
- Open files programmatically
- Execute LSE commands from scripts
- Extract editor state
- Batch operations

**LSE Command Categories:**

**1. Buffer Management:**
- `NEW BUFFER` - Create new buffer
- `GOTO BUFFER` - Switch to buffer
- `WRITE` - Save buffer
- `DELETE BUFFER` - Close buffer

**2. Navigation:**
- `GOTO LINE` - Jump to line number
- `GOTO DECLARATION` - Find definition
- `GOTO PLACEHOLDER` - Next template fill-in
- `GOTO MARK` - Jump to user mark

**3. Editing:**
- `EXPAND` - Expand template
- `CHANGE` - Search and replace
- `INDENT RANGE` - Auto-format code
- `COMMENT` - Add language-specific comments

**4. Compilation:**
- `COMPILE` - Compile current buffer
- `REVIEW` - Jump through compiler errors
- `COMPILE/ANALYSIS` - Generate SCA data

**5. Customization:**
- `DEFINE KEY` - Bind command to key
- `DEFINE TEMPLATE` - Create custom template
- `LOAD SECTION FILE` - Load initialization

## Why DECset Was Revolutionary (1980s-1990s)

**Before DECset:**
- Edit in one tool (EDT, TPU)
- Compile with separate command
- Debug with separate debugger
- Version control manual or separate tool
- No integration

**With DECset:**
- **Single environment** for entire workflow
- Tools share data (CDD, SCA database)
- **Navigate by meaning**, not just text search
- Compiler errors jump to source location
- Integrated version control

**Comparison:**

| Feature | DECset (1988) | Unix (1988) | Visual Studio (1997) |
|---------|---------------|-------------|----------------------|
| Integrated editor | ✓ LSE | ✗ (vi, emacs separate) | ✓ |
| Cross-reference DB | ✓ SCA | ✗ (ctags basic) | ✓ IntelliSense |
| Version control | ✓ CMS | SCCS, RCS (separate) | ✓ SourceSafe |
| Build automation | ✓ MMS | make (separate) | ✓ |
| Test framework | ✓ DTM | ✗ (manual) | Limited |
| Multi-language | ✓ | ✗ (Unix focused on C) | Limited |

**DECset Was Ahead of Its Time:**
- Integrated IDE before IDEs were common
- Language-aware editing (now standard)
- Cross-reference database (IntelliSense ancestor)
- Integrated testing (modern CI/CD)

## The Language-Sensitive Editor Concept

**What "Language-Sensitive" Meant:**

**1. Syntax Knowledge:**
- LSE knows Ada, C, FORTRAN, COBOL, etc. syntax
- Templates match language constructs
- Automatic indentation per language

**2. Semantic Navigation:**
- `GOTO DECLARATION` - Jump to where variable is declared
- Not just text search, but understanding code structure

**3. Context-Aware Completion:**
- Type `IF` → template expands to full if-then-else
- Type `FOR` → expands to complete loop structure
- Placeholders guide you through filling in details

**4. Compiler Integration:**
- Compile from editor
- Errors displayed in context
- Quick jump to error location

**Modern Equivalent:**
- Visual Studio IntelliSense
- Eclipse JDT
- JetBrains IDEs (IntelliJ, CLion, PyCharm)
- VS Code Language Servers (LSP)

**LSE Pioneered These Concepts in 1980s!**

## The Common Data Dictionary (CDD)

**CDD/Repository:**
- Centralized metadata repository
- Shared by all DECset tools
- Language-independent data definitions

**What's Stored:**
- Data structure definitions
- Type definitions
- Module interfaces
- Relationships between components

**Benefits:**
1. **Single source of truth** for data structures
2. **Cross-language** sharing (Ada record = C struct)
3. **Consistency** checking across modules
4. **Documentation** generation from live data

**Example Workflow:**
```
1. Define record in CDD:
   RECORD Employee
     ID : INTEGER
     NAME : STRING(50)
     SALARY : DECIMAL(10,2)

2. Generate Ada declaration from CDD
3. Generate C struct from CDD
4. Generate COBOL record from CDD
5. Generate database schema from CDD
→ All stay in sync!
```

**Modern Equivalent:**
- Protocol Buffers (protobuf)
- Apache Thrift
- Interface Definition Languages (IDL)
- OpenAPI/Swagger specifications

## Source Code Analyzer (SCA)

**The Innovation:**
Static code analysis database that persists across compilations.

**What SCA Tracks:**
- Every symbol (variable, function, type)
- Every declaration
- Every reference
- Cross-file relationships
- Call graphs
- Include dependencies

**Example Queries:**

**Find Definition:**
```
$ SCA FIND FUNCTION calculate_tax
→ Shows: FILE tax_calc.c, LINE 47
```

**Find All Uses:**
```
$ SCA FIND ALL REFERENCES calculate_tax
→ Shows every call site across entire project
```

**Call Tree:**
```
$ SCA SHOW CALL_TREE main
→ ASCII art showing what main calls, recursively
```

**Reverse Call Tree:**
```
$ SCA SHOW CALLED_BY parse_input
→ What functions call parse_input?
```

**Unused Code:**
```
$ SCA FIND SYMBOL * /UNUSED
→ Functions/variables never referenced
```

**Impact:**
- Large codebases became navigable
- Refactoring became safer
- "Dead code" easily identified
- Architecture understanding improved

**Modern Equivalent:**
- clangd (C/C++ Language Server)
- Eclipse JDT (Java)
- RustAnalyzer
- VS Code "Go to Definition" / "Find All References"

## Code Management System (CMS)

**Version Control, 1980s Style:**

**Features:**
- Element libraries (like Git repositories)
- Generations (versions)
- Variants (branches, sort of)
- Merge support
- Annotations (commit messages)

**Workflow:**
```
$ CMS CREATE LIBRARY [MYLIB]     ! Initialize repo
$ CMS CREATE ELEMENT foo.c       ! Add file
$ CMS RESERVE foo.c              ! Check out (lock)
[edit foo.c]
$ CMS REPLACE foo.c              ! Check in
$ CMS SHOW HISTORY foo.c         ! View generations
```

**Concurrent Development:**
```
User A: $ CMS RESERVE /CONCURRENT foo.c
User B: $ CMS RESERVE /CONCURRENT foo.c
[Both edit]
User A: $ CMS REPLACE foo.c
User B: $ CMS REPLACE foo.c
         → CMS prompts for merge
```

**Comparison with Modern VCS:**

| Feature | CMS (1985) | RCS (1982) | Git (2005) |
|---------|------------|------------|------------|
| Locking | Yes (default) | Yes | No (merge-based) |
| Concurrent edits | Supported | Supported | Default |
| Distributed | No | No | Yes |
| Merge | Yes | Limited | Excellent |
| Speed | Good | Good | Excellent |
| Branching | Limited (variants) | Limited | Excellent |

**CMS Limitations:**
- Centralized (no distributed development)
- Locking model (not merge-first like Git)
- VMS-specific
- Less flexible branching than Git

**But CMS Had:**
- GUI tools (VMS DECwindows)
- Integration with LSE/SCA
- Automatic tracking with MMS builds
- Part of comprehensive IDE

## Module Management System (MMS)

**Build Automation Before Modern Make:**

**MMS Description File:**
```mms
! MMS description file for my_project

my_program.exe : main.obj utils.obj
    LINK main.obj, utils.obj

main.obj : main.c headers.h
    CC /ANALYSIS main.c

utils.obj : utils.c headers.h
    CC /ANALYSIS utils.c
```

**Features:**
- Dependency tracking (like Make)
- Incremental builds (only changed files)
- CDD integration (dependencies from metadata)
- Automatic .ANA file generation for SCA
- Parallel builds (on multi-CPU systems)

**Advantages Over Unix make:**
- Native VMS file specifications
- CDD-aware (automatic dependencies)
- Better integration with compiler
- Parallel execution built-in

**Modern Equivalent:**
- CMake
- Ninja
- Bazel
- Meson

## DECset in Practice

**Typical Development Session:**

**Morning: New Feature Development**
```
$ LSE
LSE> GOTO BUFFER new_feature.c
LSE> EXPAND FUNCTION
  [Type function name, fill in template]
LSE> COMPILE/ANALYSIS
LSE> EXIT

$ SCA LOAD new_feature.ana
$ SCA VERIFY                ! Check for issues
```

**Afternoon: Integration**
```
$ CMS RESERVE new_feature.c
$ LSE new_feature.c
  [Make changes]
$ CMS REPLACE new_feature.c  "Added error handling"

$ MMS                        ! Rebuild entire project
  [MMS rebuilds only affected modules]
```

**Evening: Testing**
```
$ DTM CREATE TEST test_new_feature
$ DTM RUN test_suite
$ PCA COLLECT my_program
$ PCA SHOW COVERAGE
  [Identify untested code paths]
```

**Real-World Impact:**
- Developers could navigate million-line codebases
- Build times reduced (incremental compilation)
- Version control prevented conflicts
- Test automation caught regressions

## Why DECset Didn't Dominate

**DECset Challenges:**
- **Platform lock-in**: VMS only
- **Cost**: Expensive layered product licenses
- **Unix rising**: Workstations + free tools (gcc, make, RCS)
- **PC era**: Windows + Visual Studio

**What Survived:**
- **Concepts**: Language servers, IDEs, integrated tools
- **SCA influence**: IntelliSense, code intelligence
- **LSE templates**: Snippet systems, code generation
- **CDD concept**: Schema registries, IDLs

**Modern Descendants:**
- **Language Server Protocol (LSP)**: SCA ideas
- **Visual Studio**: Integrated IDE concept
- **JetBrains IDEs**: Language-aware editing
- **VS Code**: Extensible, language-aware editor

## The DECset Legacy

**Innovations That Became Standard:**
1. ✓ Language-aware editing (all modern IDEs)
2. ✓ Integrated debugging (standard feature)
3. ✓ Code navigation by semantics (go to definition)
4. ✓ Automated testing frameworks (standard practice)
5. ✓ Performance profiling tools (built into debuggers)

**What Didn't Survive:**
1. ✗ Centralized metadata repository (CDD)
2. ✗ Locking version control (Git's merge model won)
3. ✗ Single-vendor tool stack (open source won)

**Quote from a VMS Developer (1990s):**
> "Once you've used DECset, going back to vi and make feels like programming with stone tools."

## Modern OpenVMS and DECset

**Current Status:**
- VSI maintains DECset for OpenVMS
- Still used in legacy VMS installations
- Financial services (banks run VMS)
- Industrial control systems
- Government systems (high availability)

**VSI's Continued Development:**
- DECset ported to x86-64 (with OpenVMS)
- Updated documentation
- Integration with modern standards

## Sources

Documentation obtained from:
- VSI (VMS Software Inc.): https://vmssoftware.com/
- VMS Documentation Library
- Legacy DEC manuals (preserved at bitsavers.org)
- HP OpenVMS archives

## Further Reading

For languages supported by DECset:
- ../ada/ - Ada programming language
- ../bliss/ - BLISS systems programming language

For verified development:
- ../coq/ - Formal verification tools
- ../sel4/ - Verified OS kernel

For the operating system DECset ran on:
- OpenVMS documentation (VMS history, architecture)
- VAX/Alpha system manuals

For modern equivalents:
- Language Server Protocol (LSP) specification
- Visual Studio Code documentation
- JetBrains IDE documentation
