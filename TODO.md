# Make Syntax - Not Yet Supported

This document lists Make syntax features from various Make implementations that are not yet fully supported by the makefile-lossless parser.

## GNU Make Syntax

The following GNU Make features are not yet fully supported:

## Special Target Directives

The following special targets are recognized but not parsed with special handling:

- `.PHONY` - Marks targets that don't create actual files
- `.SUFFIXES` - Defines implicit rule suffixes
- `.PRECIOUS` - Prevents deletion of intermediate files
- `.INTERMEDIATE` - Marks files as intermediate
- `.SECONDARY` - Prevents deletion of intermediate files with no dependencies
- `.DELETE_ON_ERROR` - Deletes target file on error
- `.IGNORE` - Ignores errors in recipes
- `.LOW_RESOLUTION_TIME` - Assumes low resolution timestamps
- `.SILENT` - Suppresses recipe echoing
- `.EXPORT_ALL_VARIABLES` - Exports all variables
- `.NOTPARALLEL` - Disables parallel execution
- `.ONESHELL` - Executes all recipe lines in single shell
- `.POSIX` - Enables POSIX-compliant mode

## Variable Functions

Many GNU Make functions are not explicitly parsed or handled:

### String Functions
- `$(strip string)` - Remove leading/trailing whitespace
- `$(findstring find,in)` - Find substring
- `$(filter pattern...,text)` - Keep words matching patterns
- `$(filter-out pattern...,text)` - Remove words matching patterns
- `$(sort list)` - Sort and remove duplicates
- `$(word n,text)` - Extract nth word
- `$(wordlist s,e,text)` - Extract word range
- `$(words text)` - Count words
- `$(firstword names...)` - Get first word
- `$(lastword names...)` - Get last word

### File Name Functions
- `$(dir names...)` - Extract directory part
- `$(notdir names...)` - Remove directory part
- `$(suffix names...)` - Extract file suffixes
- `$(basename names...)` - Remove file suffixes
- `$(addsuffix suffix,names...)` - Add suffix to names
- `$(addprefix prefix,names...)` - Add prefix to names
- `$(join list1,list2)` - Join two lists pairwise
- `$(realpath names...)` - Get canonical absolute path
- `$(abspath names...)` - Get absolute path

### Control Flow Functions
- `$(if condition,then-part[,else-part])` - Conditional expansion
- `$(foreach var,list,text)` - Iterate over list
- `$(call variable,param,...)` - Call user-defined function
- `$(eval text)` - Evaluate as makefile syntax
- `$(value variable)` - Get raw variable value
- `$(origin variable)` - Get variable origin
- `$(flavor variable)` - Get variable flavor

## Advanced Conditional Features

While basic conditionals (`ifdef`, `ifndef`, `ifeq`, `ifneq`, `else`, `endif`) are supported, the following are not fully handled:

- `elif` statements (partially supported, treated similar to `else`)
- Complex conditional expressions with functions
- Nested function calls within conditionals

## Pattern Rules and Implicit Rules (Partially Supported)

- Pattern rules with `%` wildcards (e.g., `%.o: %.c`) - **BASIC SUPPORT** (parsed but no special handling)
- Static pattern rules (e.g., `objects: %.o: %.c`)
- Implicit rule chains
- `.SUFFIXES` based implicit rules
- Double-suffix rules (e.g., `.c.o:`)
- Single-suffix rules (e.g., `.c:`)

## Advanced Recipe Features

- Multi-line recipes with backslash continuation
- Recipe modifiers (`@`, `-`, `+`)
- Shell function calls within recipes
- Recipe-specific variable assignments

## Variable Assignment Operators

While basic assignment operators are supported, special handling may be missing for:

- `?=` (conditional assignment)
- `::=` (POSIX simple assignment)
- `:::=` (immediate assignment)
- `!=` (shell assignment)

## Include Directives (Partially Supported)

Basic include directives are supported, but advanced features may be missing:

- `include` directive - **SUPPORTED**
- `-include` directive (ignore errors) - **SUPPORTED**
- `sinclude` directive (synonym for `-include`) - **SUPPORTED**
- Multiple files in single include (e.g., `include file1.mk file2.mk`)
- Wildcard expansion in include paths (e.g., `include *.mk`)
- Variable expansion in include paths - **PARTIALLY SUPPORTED**

## Order-Only Prerequisites

- Syntax: `targets: normal-prerequisites | order-only-prerequisites`

## Double-Colon Rules

- Rules with `::` instead of `:` for independent rules

## Define/Endef Multi-line Variables

```make
define variable
multi-line
value
endef
```

## Automatic Variables (Partially Supported)

Special variables in recipes are recognized as variables but not specially interpreted:

- `$@` - Target name - **PARSED AS VARIABLE** (no special handling)
- `$<` - First prerequisite - **PARSED AS VARIABLE** (no special handling)
- `$^` - All prerequisites - **PARSED AS VARIABLE** (no special handling)
- `$?` - Prerequisites newer than target - **PARSED AS VARIABLE** (no special handling)
- `$*` - Stem of pattern rule - **PARSED AS VARIABLE** (no special handling)
- `$+` - All prerequisites with duplicates - **PARSED AS VARIABLE** (no special handling)
- `$|` - Order-only prerequisites - **PARSED AS VARIABLE** (no special handling)
- `$%` - Archive member - **PARSED AS VARIABLE** (no special handling)
- `$(@D)` - Directory part of target
- `$(@F)` - File part of target
- `$(<D)`, `$(<F)` - Directory/file parts of first prerequisite
- `$(^D)`, `$(^F)` - Directory/file parts of all prerequisites

## Archive Member Targets

- Syntax: `lib.a(member.o)`

## VPATH and vpath Directives

- `VPATH` variable for search paths
- `vpath` directive for pattern-specific search paths

## Target-specific Variable Assignments

```make
target: variable = value
target: variable := value
```

## Export/Unexport Directives

While `export` is partially supported, full handling may be missing for:

- `export variable`
- `unexport variable`
- `export` without arguments (export all)

## Override Directive

- `override variable = value`
- `override variable := value`

## Private Variables

- `private variable = value`

## Undefine Directive

- `undefine variable`

## GNU Make Specific Extensions

- `.RECIPEPREFIX` - Change recipe prefix character
- `.SHELLFLAGS` - Flags for shell invocation
- `MAKECMDGOALS` - Command line targets
- `.FEATURES` - Available GNU Make features
- `.INCLUDE_DIRS` - Include search directories

## BSD Make Syntax

BSD Make (bmake/pmake) specific features not yet supported:

### Variable Modifiers
- `:U` - Use default value if undefined
- `:D` - Use value if defined
- `:L` - Lowercase conversion
- `:U` - Uppercase conversion
- `:M` - Match pattern
- `:N` - Exclude pattern
- `:O` - Order alphabetically
- `:Q` - Quote shell meta-characters
- `:R` - Reverse order
- `:S/old/new/` - Substitution
- `:T` - Tail (basename)
- `:H` - Head (dirname)
- `:E` - Extension
- `:C/regex/replacement/` - Regex substitution
- `:hash` - Hash value
- `:range[=sep]` - Generate numeric range
- `:ts` - Change separator

### Conditional Operators
- `.if`, `.elif`, `.else`, `.endif` - BSD-style conditionals
- `.ifdef`, `.ifndef` - BSD-style defined checks
- `.ifmake` - Check if target is being made
- `.ifnmake` - Check if target is not being made
- Conditional operators: `==`, `!=`, `>`, `>=`, `<`, `<=`, `&&`, `||`, `!`

### Loop Constructs
- `.for` variable `in` list / `.endfor` - BSD-style loops

### Include Directives
- `.include "file"` - BSD-style include
- `.include <file>` - System include
- `.sinclude` - Silent include

### Special Variables
- `.CURDIR` - Current directory
- `.OBJDIR` - Object directory
- `.TARGETS` - Command line targets
- `.ALLSRC` - All sources (like `$^`)
- `.IMPSRC` - Implied source
- `.PREFIX` - Prefix of target
- `.ARCHIVE` - Archive name
- `.MEMBER` - Archive member
- `.OODATE` - Out-of-date prerequisites

### Special Targets
- `.BEGIN` - Run before anything else
- `.END` - Run after everything else
- `.ERROR` - Run on error
- `.INTERRUPT` - Run on interrupt
- `.MAIN` - Default target
- `.MAKEFLAGS` - Flags to pass to sub-makes
- `.MFLAGS` - Another way to pass flags
- `.NOTMAIN` - Not the main target
- `.OPTIONAL` - Optional dependencies
- `.ORDER` - Order dependencies
- `.PATH` - Search path for files
- `.SHELL` - Shell to use

## POSIX Make Syntax

POSIX-compliant features that may not be fully supported:

### Inference Rules
- `.c.o:` - Suffix rules
- Single suffix rules (`.c:`)
- Double suffix rules (`.c.o:`)

### Macro String Substitution
- `$(macro:str1=str2)` - Substitution in expansion

### Internal Macros
- `$$@` - Current target (in prerequisites)
- `$$<` - Current dependency
- `$$*` - Current stem

### Special Targets
- `.DEFAULT` - Default rule
- `.IGNORE` - Ignore errors
- `.PRECIOUS` - Don't delete on interrupt
- `.SILENT` - Don't echo commands
- `.SUFFIXES` - List of suffixes
- `.SCCS_GET` - SCCS retrieval

## Microsoft NMAKE Syntax

NMAKE-specific features not supported:

### Preprocessing Directives
- `!IF` / `!ELSEIF` / `!ELSE` / `!ENDIF` - Conditionals
- `!IFDEF` / `!IFNDEF` - Defined checks
- `!ERROR` - Generate error
- `!MESSAGE` - Display message
- `!INCLUDE` - Include file
- `!CMDSWITCHES` - Set command switches
- `!UNDEF` - Undefine macro

### Special Macros
- `$?` - Dependencies newer than target
- `$**` - All dependencies
- `$$@` - Current target (full path)
- `$(**)` - All dependencies (full paths)
- `$<` - Dependency in inference rule
- `$(?)` - Dependencies newer than target (full paths)

### Filename Macros and Modifiers
- `$(@D)` - Directory of target
- `$(@B)` - Base name of target
- `$(@F)` - File name of target
- `$(@R)` - File name without extension

### Batch Mode Rules
- `{frompath}.fromext{topath}.toext::` - Batch inference rules

### Inline Files
```nmake
target: dependency
    command <<filename
inline file contents
<<
```

### Directives
- `.IGNORE:` - Ignore errors
- `.PRECIOUS:` - Keep files
- `.SILENT:` - Suppress echo
- `.SUFFIXES:` - Define suffixes

## SunOS/Solaris Make

Solaris Make specific features:

### Special Targets
- `.KEEP_STATE` - Automatic dependency checking
- `.PARALLEL` - Parallel execution rules
- `.NO_PARALLEL` - Disable parallel execution
- `.WAIT` - Synchronization point
- `.SCCS_GET` - SCCS retrieval rules

### Conditional Macros
- `:=` - Conditional macro assignment
- `target := macro = value` - Target-specific conditional assignment

### Special Macros
- `$$%` - Member of archive library

## AIX Make

AIX Make specific features:

### Special Targets
- `.NOEXPORT` - Don't export variables
- `.MAKE` - Always execute

### Variable References
- `${variable:modifier}` - AIX-specific modifiers

## Additional GNU Make Features Not Supported

### Secondary Expansion
- `.SECONDEXPANSION` - Enable secondary expansion
- `$$` in prerequisites for second expansion

### Guile Integration
- `$(guile ...)` - Embedded Guile Scheme code

### Load Directive
- `load` - Load dynamic extensions

### Output Synchronization
- `.NOTPARALLEL` - Disable parallel execution
- `--output-sync` - Synchronized output in parallel builds

### Job Server
- `+` command prefix for recursive make
- `$(MAKE)` variable for recursive invocation

### Text Transformation Functions
- `$(info text)` - Print information message
- `$(warning text)` - Print warning message
- `$(error text)` - Print error and stop

### File Functions
- `$(file op filename[,text])` - File operations
- `$(file >filename,text)` - Write to file
- `$(file >>filename,text)` - Append to file
- `$(file <filename)` - Read from file

### Debugging Features
- `$(info ...)`, `$(warning ...)`, `$(error ...)` - Debugging output
- `.SHELLSTATUS` - Exit status of last shell command

## Makefile Parsing Limitations

### Comments
- Comments within variable definitions may not be handled correctly
- Escaped newlines in comments

### Line Continuations
- Complex line continuations with mixed tabs and spaces
- Line continuations in conditional expressions

### Shell Integration
- Complex shell escaping
- Nested shell command substitutions
- Shell-specific syntax within recipes

### Globbing and Wildcards
- Advanced globbing patterns
- Recursive wildcards (`**`)

### Unicode and Encoding
- Non-UTF-8 encodings
- Unicode in target/variable names

## Notes

The parser currently focuses on preserving the structure and content of makefiles for lossless round-tripping. Many of these features are preserved in the output but may not have specialized parsing or manipulation APIs. The parser is designed to be permissive and will attempt to parse makefiles with these features without failing, even if it doesn't fully understand their semantics.

Different Make implementations have incompatible syntax and features. This parser primarily targets GNU Make syntax while attempting to be flexible enough to handle common patterns from other implementations.

### Supported Features Summary

The parser **does** support:
- Basic rules with targets, prerequisites, and recipes
- Variable definitions (`=`, `:=`, `+=`)
- Variable references (`$(VAR)`, `${VAR}`)
- Comments (`#`)
- Basic conditionals (`ifdef`, `ifndef`, `ifeq`, `ifneq`, `else`, `endif`)
- Include directives (`include`, `-include`, `sinclude`)
- Export directives (basic form)
- `.PHONY` targets (parsed as regular rules)
- Pattern rules with `%` (basic parsing)
- Shell function calls (`$(shell ...)`)
- Most GNU Make functions (preserved but not interpreted)