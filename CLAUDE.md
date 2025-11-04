# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Overview

This repository contains two main components:

1. **BFO Project** (`bfo-project/`) - Basic Formal Ontology (BFO) research and validation
2. **MCP File System Server** (`mcp_server_filesystem/`) - A Model Context Protocol server for file operations

## Key Components

### BFO Project (`bfo-project/`)

The BFO project focuses on formal validation of Basic Formal Ontology axioms using automated reasoning tools.

**Core Files:**
- `bfo.owl` - The main BFO ontology in OWL format
- `bfo.json` - JSON representation of the ontology (large file, 51k+ tokens)
- `bfo_z3_validation.py` - Real Z3 SMT solver validation of BFO axioms
- `bfo_validation_demo.py` - Simulation/demo of validation process
- `owl_to_json.py` - Converts OWL XML format to JSON
- `fol_axioms.json` - First-order logic axioms extracted from BFO
- `classes-annotations-human-readable.json` - Human-readable class annotations
- `*.smt2` files - SMT-LIB format axioms for Z3 solver
- `z3_validation_summary.md` - Results and findings from Z3 validation

**Architecture:**
- **Ontology Processing**: `owl_to_json.py` parses OWL XML into structured JSON
- **Axiom Extraction**: Formal axioms are extracted into FOL and SMT-LIB formats
- **Validation Engine**: `bfo_z3_validation.py` uses Z3 to formally verify axiom consistency
- **Demo System**: `bfo_validation_demo.py` simulates validation for systems without Z3

**Key Findings:**
The BFO validation has proven that:
- BFO Core axioms are logically consistent
- Type hierarchies work correctly (Process → Occurrent, etc.)
- Disjointness constraints are preserved (Continuant ⊥ Occurrent)
- Mereological properties maintain type consistency

### MCP File System Server (`mcp_server_filesystem/`)

A Python-based Model Context Protocol server that provides secure file system operations for AI assistants.

**Architecture:**
```
src/
├── main.py              # Entry point with CLI argument parsing
├── server.py            # MCP server implementation using FastMCP
├── log_utils.py         # Structured logging configuration
└── file_tools/          # File operation tools
    ├── file_operations.py    # Core file read/write operations
    ├── edit_file.py         # Advanced pattern-based file editing
    ├── directory_utils.py   # Directory listing and management
    └── path_utils.py        # Path validation and security
```

**Testing:**
- `tests/` contains comprehensive pytest test suite
- `tests/testdata/` provides test fixtures
- `tests/LLM_Test.md` contains instructions for LLM-based testing

## Development Commands

### BFO Project

**Running Validations:**
```bash
# Real Z3 validation (requires z3-solver package)
cd bfo-project
python bfo_z3_validation.py

# Demo validation (no dependencies)
python bfo_validation_demo.py

# Convert OWL to JSON
python owl_to_json.py
```

**Dependencies:**
- `z3-solver` for real SMT validation
- Standard library for demo/conversion scripts

### MCP File System Server

**Development Setup:**
```bash
cd mcp_server_filesystem

# Create virtual environment
python -m venv .venv
source .venv/bin/activate  # On Windows: .venv\Scripts\activate

# Install in development mode
pip install -e ".[dev]"
```

**Running the Server:**
```bash
# Basic usage
python -m src.main --project-dir /path/to/project

# With logging options
python -m src.main --project-dir /path/to/project --log-level DEBUG --log-file server.log
```

**Testing:**
```bash
# Run all tests
pytest

# Run specific test categories
pytest tests/file_tools/
pytest tests/test_server.py

# Run with coverage
pytest --cov=src
```

**Code Quality:**
```bash
# Format code
black src/ tests/

# Sort imports
isort src/ tests/

# Lint code
pylint src/

# Type checking (if mypy is available)
mypy src/
```

## Integration Notes

### MCP Server Integration

The MCP server can be integrated with:

**Claude Desktop:**
- Configuration: `~/Library/Application Support/Claude/claude_desktop_config.json` (macOS)
- Configuration: `%APPDATA%\Claude\claude_desktop_config.json` (Windows)

**VSCode/Cline Extension:**
- Configuration: Uses Cline MCP settings file
- Auto-approval recommended for `list_directory` and `read_file` operations

**Available Tools:**
- `list_directory` - List files and directories
- `read_file` - Read file contents
- `save_file` - Write files atomically
- `append_file` - Append to existing files
- `delete_this_file` - Delete files
- `edit_file` - Advanced pattern-based editing with diff output

### Security Features

- All file operations are restricted to the specified project directory
- Path traversal attacks are prevented through validation
- Atomic file operations prevent corruption
- Structured logging tracks all operations

## Important Files to Understand

1. **`bfo-project/z3_validation_summary.md`** - Contains key findings from formal validation
2. **`mcp_server_filesystem/src/server.py`** - Main MCP server logic
3. **`mcp_server_filesystem/src/file_tools/edit_file.py`** - Advanced file editing capabilities
4. **`bfo-project/bfo_z3_validation.py`** - Real SMT solver validation implementation

## Project Goals

**BFO Project:**
- Formal verification of philosophical ontology concepts
- Bridge between abstract metaphysics and concrete mathematics
- Provide validated foundations for AI reasoning systems

**MCP Server:**
- Enable AI assistants to safely interact with local file systems
- Provide structured, secure file operations
- Support collaborative AI-human development workflows