# BFO (Basic Formal Ontology) - Formal Validation Project

A comprehensive project for formal validation of **Basic Formal Ontology (BFO)** axioms using automated reasoning tools, with interactive visualizations.

[![Z3 Validated](https://img.shields.io/badge/Z3-Validated-brightgreen)](https://github.com/Z3Prover/z3)
[![BFO Classes](https://img.shields.io/badge/BFO_Classes-35-blue)](docs/index.html)
[![FOL Axioms](https://img.shields.io/badge/FOL_Axioms-51-orange)](bfo-project/fol_axioms.json)

## Start Here

Choose your path:

**→ [Explore the Interactive Visualization](https://rasinj.github.io/bfo/)** - Best for understanding the BFO hierarchy visually

**→ [Run the Validation](#quick-start)** - For developers wanting to verify BFO axioms with Z3

**→ [Learn About BFO](#what-is-bfo)** - For newcomers to formal ontology

## What is BFO?

**Basic Formal Ontology (BFO)** is a top-level ontology designed to support information integration and semantic interoperability across scientific disciplines. It provides a formal framework for categorizing all entities in reality into two fundamental types:

- **Continuants**: Entities that persist through time while maintaining their identity (objects, qualities, etc.)
- **Occurrents**: Entities that unfold in time (processes, events, etc.)

BFO is widely used in biomedical informatics, scientific databases, and AI reasoning systems.

## Interactive Visualization

Explore all 35 BFO classes in an interactive hierarchical tree:

**[Launch Interactive Visualization](https://rasinj.github.io/bfo/)** *(Click to expand/collapse • Hover for details)*

[![BFO Hierarchy Visualization](docs/bfo-hierarchy-preview.png)](https://rasinj.github.io/bfo/)

*Click the image above or the link to explore the interactive version*

### Visualization Features

- **Interactive**: Click nodes to expand/collapse branches
- **Color-coded**: Different entity types have distinct colors
- **Detailed tooltips**: Hover over nodes for definitions and examples
- **35 Classes**: Complete BFO hierarchy from Entity to leaf concepts
- **Pan & Zoom**: Drag to pan, scroll to zoom
- **Responsive**: Works on desktop and mobile devices

## Project Overview

### Key Components

```
bfo-project/
├── bfo.owl                    # BFO ontology (OWL XML format, 157KB)
├── bfo.json                   # BFO in JSON format (155KB)
├── classes-annotations-human-readable.json  # 35 BFO classes with definitions (75KB)
├── fol_axioms.json           # 51 First-Order Logic axioms
├── bfo_z3_validation.py      # Real Z3 SMT solver validation
├── bfo_validation_demo.py    # Demo version (no dependencies)
└── z3_validation_summary.md  # Validation results & findings
```

### The 35 BFO Classes

BFO organizes all entities into a clear hierarchy:

```
Entity (root)
├── Continuant (persists through time)
│   ├── Independent Continuant
│   │   ├── Material Entity (Object, Fiat Object Part, Object Aggregate)
│   │   ├── Immaterial Entity (Site, Continuant Fiat Boundary)
│   │   └── Spatial Region (0D, 1D, 2D, 3D)
│   ├── Specifically Dependent Continuant
│   │   ├── Quality (Relational Quality)
│   │   └── Realizable Entity (Disposition, Function, Role)
│   └── Generically Dependent Continuant
│
└── Occurrent (unfolds in time)
    ├── Process (Process Boundary, Process Profile, History)
    ├── Temporal Region (0D, 1D)
    └── Spatiotemporal Region
```

## Formal Validation

This project uses the **Z3 SMT Solver** to formally verify BFO's logical consistency. All 51 First-Order Logic axioms have been proven consistent through automated theorem proving.

### Validation Coverage

| Validation Test | Status | Details |
|----------------|---------|---------|
| **Axiom Consistency** | PASS | All 51 FOL axioms are logically consistent |
| **Type Hierarchies** | PASS | Process → Occurrent → Entity |
| **Disjointness Constraints** | PASS | Continuant ⊥ Occurrent (mutually exclusive) |
| **Expected Entailments** | PASS | All processes are occurrents |
| **Mereological Properties** | PASS | Part-whole relations maintain type consistency |

The validation demonstrates that BFO's core axioms are logically sound, with no contradictions found in the tested axiom set. Type hierarchies work as specified, fundamental categories are properly separated, and all definitions are well-formed.

See [z3_validation_summary.md](bfo-project/z3_validation_summary.md) for detailed validation results.

## Quick Start

### For Users

```bash
cd bfo-project

# Install dependencies
pip install z3-solver

# Run Z3 validation
python bfo_z3_validation.py

# Or run demo version (no dependencies)
python bfo_validation_demo.py
```

### For Developers

```bash
# One-time setup (installs dependencies and pre-commit hooks)
./setup-dev.sh

# Pre-commit hooks will automatically run validation before each commit
# To manually run all checks:
pre-commit run --all-files
```

### Explore the Data

```bash
# View all 35 BFO classes with definitions and examples
cat bfo-project/classes-annotations-human-readable.json

# View the 51 First-Order Logic axioms
cat bfo-project/fol_axioms.json

# Convert OWL to JSON (if needed)
python bfo-project/owl_to_json.py
```

### View Visualization Locally

```bash
cd docs
python -m http.server 8000
# Open http://localhost:8000 in your browser
```

## Project Statistics

- **35 BFO Classes**: Complete hierarchy from top-level Entity to leaf concepts
- **51 FOL Axioms**: Extracted from BFO 2.0 CLIF specification
- **100% Validated**: All axioms proven consistent via Z3 SMT solver
- **Real Examples**: Each class includes real-world examples
- **Interactive Visualization**: Explore the full hierarchy dynamically

## Technical Details

### Axiom Types Validated

- **Subsumption axioms**: Class hierarchies (e.g., `Process → Occurrent → Entity`)
- **Disjointness axioms**: Mutual exclusivity (e.g., `Continuant ⊥ Occurrent`)
- **Definition axioms**: Biconditional definitions (e.g., Process definition)
- **Property axioms**: Mereological closure, temporal properties
- **Dependency axioms**: Specific dependence relations

### SMT Solver Validation

The Z3 SMT solver provides:
- **Formal mathematical proofs** (not heuristics)
- **Model generation** for satisfiable axioms
- **Counterexample detection** for invalid entailments
- **Handling of quantified formulas** (∀, ∃)

## Learn More About BFO

- **Official BFO Website**: [https://basic-formal-ontology.org/](https://basic-formal-ontology.org/)
- **BFO 2.0 Reference**: Complete specification and documentation
- **Applications**: Medical informatics, scientific databases, AI reasoning
- **Use Cases**: Gene Ontology (GO), OBO Foundry ontologies

## Visualization Technology

The interactive visualization uses:
- **D3.js v7**: Hierarchical tree layout with smooth animations
- **Responsive Design**: Works on all screen sizes
- **Color Scheme**: Semantic color coding by entity type
- **Interactive Tooltips**: Detailed information on hover
- **Pan & Zoom**: Full navigation support

## Continuous Integration

The project includes automated validation through:

### GitHub Actions
- Runs on every push and pull request
- Validates all 51 FOL axioms using Z3
- Generates visualization files
- Ensures data integrity

See [.github/workflows/validate.yml](.github/workflows/validate.yml) for details.

### Pre-commit Hooks
- Automatically validates BFO axioms before each commit
- Checks JSON file integrity
- Verifies visualization files exist
- Prevents commits with validation failures

Install with: `./setup-dev.sh` or `pre-commit install`

## Contributing

Contributions are welcome! Areas for contribution:
- Additional validation tests
- Enhanced visualizations
- Documentation improvements
- BFO application examples

All contributions must pass:
- Z3 validation tests
- Pre-commit hooks
- GitHub Actions CI checks

## License

This project is provided for research and educational purposes.

## Acknowledgments

- **BFO Development Team**: For creating and maintaining BFO
- **Z3 Theorem Prover**: For powerful SMT solving capabilities
- **D3.js Community**: For excellent visualization library

---

**Note**: This project demonstrates that BFO has solid logical foundations suitable for deployment in AI systems, medical informatics, and scientific databases. The formal validation gives confidence that BFO-based systems won't encounter logical paradoxes or inconsistencies.

**Explore the interactive visualization**: [https://rasinj.github.io/bfo/](https://rasinj.github.io/bfo/)
