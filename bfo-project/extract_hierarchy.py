#!/usr/bin/env python3
"""
Extract BFO class hierarchy for visualization
Generates a tree structure suitable for D3.js
"""

import json
import re

def parse_bfo_classes(json_file):
    """Parse BFO classes from JSON and build hierarchy"""

    with open(json_file, 'r') as f:
        content = f.read()

    # Split by class entries (each starts with a complete JSON object)
    classes = []
    current = ""
    brace_count = 0

    for char in content:
        current += char
        if char == '{':
            brace_count += 1
        elif char == '}':
            brace_count -= 1
            if brace_count == 0 and current.strip():
                try:
                    obj = json.loads(current.strip())
                    classes.append(obj)
                    current = ""
                except json.JSONDecodeError:
                    pass

    return classes

def build_hierarchy():
    """Build the BFO class hierarchy tree"""

    # Define the complete BFO hierarchy structure
    hierarchy = {
        "name": "entity",
        "label": "Entity",
        "iri": "http://purl.obolibrary.org/obo/BFO_0000001",
        "description": "Anything that exists or has existed or will exist",
        "examples": ["Julius Caesar", "the Second World War", "your body mass index"],
        "type": "root",
        "children": [
            {
                "name": "continuant",
                "label": "Continuant",
                "iri": "http://purl.obolibrary.org/obo/BFO_0000002",
                "description": "An entity that persists through time while maintaining its identity",
                "type": "continuant",
                "children": [
                    {
                        "name": "independent-continuant",
                        "label": "Independent Continuant",
                        "iri": "http://purl.obolibrary.org/obo/BFO_0000004",
                        "description": "A continuant that does not depend specifically on any other entity",
                        "type": "continuant",
                        "children": [
                            {
                                "name": "material-entity",
                                "label": "Material Entity",
                                "iri": "http://purl.obolibrary.org/obo/BFO_0000040",
                                "description": "An independent continuant with matter as part",
                                "type": "material",
                                "children": [
                                    {
                                        "name": "object",
                                        "label": "Object",
                                        "iri": "http://purl.obolibrary.org/obo/BFO_0000030",
                                        "description": "A material entity with causal unity",
                                        "examples": ["atom", "cell", "organism", "planet", "engineered artifacts"],
                                        "type": "material"
                                    },
                                    {
                                        "name": "fiat-object-part",
                                        "label": "Fiat Object Part",
                                        "iri": "http://purl.obolibrary.org/obo/BFO_0000024",
                                        "description": "A material entity demarcated by fiat boundaries",
                                        "examples": ["the Western hemisphere", "upper lobe of left lung", "your torso"],
                                        "type": "material"
                                    },
                                    {
                                        "name": "object-aggregate",
                                        "label": "Object Aggregate",
                                        "iri": "http://purl.obolibrary.org/obo/BFO_0000027",
                                        "description": "A material entity consisting of multiple objects",
                                        "examples": ["a swarm of bees", "a symphony orchestra", "blood cells in your body"],
                                        "type": "material"
                                    }
                                ]
                            },
                            {
                                "name": "immaterial-entity",
                                "label": "Immaterial Entity",
                                "iri": "http://purl.obolibrary.org/obo/BFO_0000141",
                                "description": "An independent continuant without matter",
                                "type": "immaterial",
                                "children": [
                                    {
                                        "name": "site",
                                        "label": "Site",
                                        "iri": "http://purl.obolibrary.org/obo/BFO_0000029",
                                        "description": "A 3D immaterial entity bounded by material entities",
                                        "examples": ["a hole in cheese", "the Grand Canyon", "interior of your mouth"],
                                        "type": "immaterial"
                                    },
                                    {
                                        "name": "continuant-fiat-boundary",
                                        "label": "Continuant Fiat Boundary",
                                        "iri": "http://purl.obolibrary.org/obo/BFO_0000140",
                                        "description": "An immaterial boundary of 0, 1, or 2 dimensions",
                                        "type": "immaterial",
                                        "children": [
                                            {
                                                "name": "0d-cf-boundary",
                                                "label": "0D Continuant Fiat Boundary",
                                                "iri": "http://purl.obolibrary.org/obo/BFO_0000147",
                                                "description": "A fiat point",
                                                "examples": ["the North Pole", "quadripoint of four US states"],
                                                "type": "immaterial"
                                            },
                                            {
                                                "name": "1d-cf-boundary",
                                                "label": "1D Continuant Fiat Boundary",
                                                "iri": "http://purl.obolibrary.org/obo/BFO_0000142",
                                                "description": "A continuous fiat line",
                                                "examples": ["the Equator", "geopolitical boundaries", "lines of latitude"],
                                                "type": "immaterial"
                                            },
                                            {
                                                "name": "2d-cf-boundary",
                                                "label": "2D Continuant Fiat Boundary",
                                                "iri": "http://purl.obolibrary.org/obo/BFO_0000146",
                                                "description": "A self-connected fiat surface",
                                                "examples": ["surface boundaries of hemispheres"],
                                                "type": "immaterial"
                                            }
                                        ]
                                    }
                                ]
                            },
                            {
                                "name": "spatial-region",
                                "label": "Spatial Region",
                                "iri": "http://purl.obolibrary.org/obo/BFO_0000006",
                                "description": "A continuant part of space",
                                "type": "region",
                                "children": [
                                    {
                                        "name": "0d-spatial-region",
                                        "label": "0D Spatial Region",
                                        "iri": "http://purl.obolibrary.org/obo/BFO_0000018",
                                        "description": "A point in space",
                                        "type": "region"
                                    },
                                    {
                                        "name": "1d-spatial-region",
                                        "label": "1D Spatial Region",
                                        "iri": "http://purl.obolibrary.org/obo/BFO_0000026",
                                        "description": "A line in space",
                                        "examples": ["edge of a cube"],
                                        "type": "region"
                                    },
                                    {
                                        "name": "2d-spatial-region",
                                        "label": "2D Spatial Region",
                                        "iri": "http://purl.obolibrary.org/obo/BFO_0000009",
                                        "description": "A surface in space",
                                        "examples": ["surface of a sphere"],
                                        "type": "region"
                                    },
                                    {
                                        "name": "3d-spatial-region",
                                        "label": "3D Spatial Region",
                                        "iri": "http://purl.obolibrary.org/obo/BFO_0000028",
                                        "description": "A volume in space",
                                        "examples": ["a cube-shaped region", "a sphere-shaped region"],
                                        "type": "region"
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        "name": "specifically-dependent-continuant",
                        "label": "Specifically Dependent Continuant",
                        "iri": "http://purl.obolibrary.org/obo/BFO_0000020",
                        "description": "A continuant that depends on specific independent continuants",
                        "type": "continuant",
                        "children": [
                            {
                                "name": "quality",
                                "label": "Quality",
                                "iri": "http://purl.obolibrary.org/obo/BFO_0000019",
                                "description": "A specifically dependent continuant not requiring a process to be realized",
                                "examples": ["color of a tomato", "mass of gold", "shape of your nose"],
                                "type": "quality",
                                "children": [
                                    {
                                        "name": "relational-quality",
                                        "label": "Relational Quality",
                                        "iri": "http://purl.obolibrary.org/obo/BFO_0000145",
                                        "description": "A quality with multiple bearers",
                                        "examples": ["a marriage bond", "an obligation between persons"],
                                        "type": "quality"
                                    }
                                ]
                            },
                            {
                                "name": "realizable-entity",
                                "label": "Realizable Entity",
                                "iri": "http://purl.obolibrary.org/obo/BFO_0000017",
                                "description": "A specifically dependent continuant realized in processes",
                                "type": "realizable",
                                "children": [
                                    {
                                        "name": "disposition",
                                        "label": "Disposition",
                                        "iri": "http://purl.obolibrary.org/obo/BFO_0000016",
                                        "description": "A realizable entity realized in special physical circumstances",
                                        "examples": ["disposition to decay", "fragility", "predisposition to cancer"],
                                        "type": "realizable",
                                        "children": [
                                            {
                                                "name": "function",
                                                "label": "Function",
                                                "iri": "http://purl.obolibrary.org/obo/BFO_0000034",
                                                "description": "A disposition existing due to design or evolution",
                                                "examples": ["function of heart to pump", "function of hammer to drive nails"],
                                                "type": "realizable"
                                            }
                                        ]
                                    },
                                    {
                                        "name": "role",
                                        "label": "Role",
                                        "iri": "http://purl.obolibrary.org/obo/BFO_0000023",
                                        "description": "A realizable entity depending on special circumstances",
                                        "examples": ["role of being a doctor", "student role", "priest role"],
                                        "type": "realizable"
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        "name": "generically-dependent-continuant",
                        "label": "Generically Dependent Continuant",
                        "iri": "http://purl.obolibrary.org/obo/BFO_0000031",
                        "description": "A continuant generically depending on other entities",
                        "examples": ["a PDF file", "protein sequence", "database entries"],
                        "type": "continuant"
                    }
                ]
            },
            {
                "name": "occurrent",
                "label": "Occurrent",
                "iri": "http://purl.obolibrary.org/obo/BFO_0000003",
                "description": "An entity that unfolds in time or is a temporal/spatiotemporal region",
                "type": "occurrent",
                "children": [
                    {
                        "name": "process",
                        "label": "Process",
                        "iri": "http://purl.obolibrary.org/obo/BFO_0000015",
                        "description": "An occurrent with temporal parts depending on material entities",
                        "examples": ["cell division", "sleeping", "the life of an organism", "your aging"],
                        "type": "process",
                        "children": [
                            {
                                "name": "process-boundary",
                                "label": "Process Boundary",
                                "iri": "http://purl.obolibrary.org/obo/BFO_0000035",
                                "description": "A temporal part of a process with no proper temporal parts",
                                "examples": ["boundary between 2nd and 3rd year of life"],
                                "type": "process"
                            },
                            {
                                "name": "process-profile",
                                "label": "Process Profile",
                                "iri": "http://purl.obolibrary.org/obo/BFO_0000144",
                                "description": "A process characterized by measurable changes",
                                "examples": ["speed profile", "temperature change profile"],
                                "type": "process"
                            },
                            {
                                "name": "history",
                                "label": "History",
                                "iri": "http://purl.obolibrary.org/obo/BFO_0000182",
                                "description": "Sum of all processes in a spatiotemporal region",
                                "type": "process"
                            }
                        ]
                    },
                    {
                        "name": "temporal-region",
                        "label": "Temporal Region",
                        "iri": "http://purl.obolibrary.org/obo/BFO_0000008",
                        "description": "An occurrent that is part of time",
                        "type": "occurrent",
                        "children": [
                            {
                                "name": "0d-temporal-region",
                                "label": "0D Temporal Region",
                                "iri": "http://purl.obolibrary.org/obo/BFO_0000148",
                                "description": "A temporal region without extent (instant)",
                                "examples": ["right now", "moment of birth", "moment of death"],
                                "type": "occurrent"
                            },
                            {
                                "name": "1d-temporal-region",
                                "label": "1D Temporal Region",
                                "iri": "http://purl.obolibrary.org/obo/BFO_0000038",
                                "description": "An extended temporal region (interval)",
                                "examples": ["temporal region during which a process occurs"],
                                "type": "occurrent"
                            }
                        ]
                    },
                    {
                        "name": "spatiotemporal-region",
                        "label": "Spatiotemporal Region",
                        "iri": "http://purl.obolibrary.org/obo/BFO_0000011",
                        "description": "An occurrent that is part of spacetime",
                        "examples": ["region occupied by a human life", "region occupied by cellular meiosis"],
                        "type": "occurrent"
                    }
                ]
            }
        ]
    }

    return hierarchy

if __name__ == "__main__":
    hierarchy = build_hierarchy()

    # Save to JSON file for D3.js
    output_file = "/home/user/bfo/docs/bfo-hierarchy.json"
    with open(output_file, 'w') as f:
        json.dump(hierarchy, f, indent=2)

    print(f"✓ BFO hierarchy saved to {output_file}")
    print(f"✓ Total classes in hierarchy: 35")
