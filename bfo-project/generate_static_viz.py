#!/usr/bin/env python3
"""
Generate a static SVG visualization of the BFO hierarchy
"""

import json

def generate_svg_tree():
    """Generate a static SVG tree visualization"""

    # Load hierarchy
    with open('/home/user/bfo/docs/bfo-hierarchy.json', 'r') as f:
        data = json.load(f)

    # Color scheme
    colors = {
        'root': '#667eea',
        'continuant': '#4299e1',
        'occurrent': '#f6ad55',
        'material': '#48bb78',
        'immaterial': '#a0aec0',
        'region': '#cbd5e0',
        'quality': '#9f7aea',
        'realizable': '#b794f4',
        'process': '#ed64a6'
    }

    # SVG dimensions
    width = 1600
    height = 2400
    node_radius = 8
    vertical_spacing = 40
    horizontal_spacing = 300

    svg_parts = []
    svg_parts.append(f'<?xml version="1.0" encoding="UTF-8"?>')
    svg_parts.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">')

    # Background
    svg_parts.append(f'<rect width="{width}" height="{height}" fill="white"/>')

    # Title
    svg_parts.append(f'<text x="{width//2}" y="40" text-anchor="middle" font-size="32" font-weight="bold" font-family="Arial, sans-serif" fill="#333">BFO (Basic Formal Ontology) Hierarchy</text>')
    svg_parts.append(f'<text x="{width//2}" y="70" text-anchor="middle" font-size="16" font-family="Arial, sans-serif" fill="#666">35 Classes • 51 FOL Axioms • Z3 Validated</text>')

    # Legend
    legend_y = 100
    legend_x = 50
    svg_parts.append(f'<text x="{legend_x}" y="{legend_y}" font-size="14" font-weight="bold" font-family="Arial, sans-serif" fill="#333">Legend:</text>')

    legend_items = [
        ('Continuant', 'continuant'),
        ('Occurrent', 'occurrent'),
        ('Material', 'material'),
        ('Quality/Realizable', 'quality'),
        ('Process', 'process'),
    ]

    for i, (label, type_key) in enumerate(legend_items):
        x = legend_x + 80 + (i * 150)
        svg_parts.append(f'<circle cx="{x}" cy="{legend_y-5}" r="8" fill="{colors[type_key]}" stroke="#333" stroke-width="2"/>')
        svg_parts.append(f'<text x="{x+15}" y="{legend_y}" font-size="12" font-family="Arial, sans-serif" fill="#666">{label}</text>')

    # Start tree from here
    tree_start_y = 150

    def draw_node(node, x, y, depth, parent_x=None, parent_y=None):
        """Recursively draw tree nodes"""
        nonlocal svg_parts

        color = colors.get(node.get('type', 'root'), '#999')

        # Draw connection line from parent
        if parent_x is not None and parent_y is not None:
            svg_parts.append(f'<path d="M {parent_x} {parent_y} C {parent_x} {(parent_y + y)/2}, {x} {(parent_y + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')

        # Draw node circle
        svg_parts.append(f'<circle cx="{x}" cy="{y}" r="{node_radius}" fill="{color}" stroke="#333" stroke-width="2"/>')

        # Draw label
        label = node.get('label', node.get('name', ''))
        label_x = x + 15
        svg_parts.append(f'<text x="{label_x}" y="{y + 5}" font-size="13" font-family="Arial, sans-serif" fill="#333">{label}</text>')

        # Draw children
        if 'children' in node and node['children']:
            children = node['children']
            child_y = y + vertical_spacing

            # Calculate total width needed for children
            if len(children) == 1:
                child_x = x
                draw_node(children[0], child_x, child_y, depth + 1, x, y)
            else:
                # Distribute children horizontally
                for i, child in enumerate(children):
                    child_x = x - (len(children) - 1) * 60 + i * 120
                    draw_node(child, child_x, child_y, depth + 1, x, y)

    # Calculate positions for main branches
    root_x = width // 2
    root_y = tree_start_y

    # Draw root
    root_color = colors['root']
    svg_parts.append(f'<circle cx="{root_x}" cy="{root_y}" r="{node_radius}" fill="{root_color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{root_x + 15}" y="{root_y + 5}" font-size="14" font-weight="bold" font-family="Arial, sans-serif" fill="#333">{data["label"]}</text>')

    # Draw two main branches: Continuant and Occurrent
    if 'children' in data:
        continuant = data['children'][0]
        occurrent = data['children'][1]

        # Continuant branch (left)
        cont_x = 400
        cont_y = root_y + 60

        # Occurrent branch (right)
        occ_x = 1200
        occ_y = root_y + 60

        # Draw connections from root
        svg_parts.append(f'<path d="M {root_x} {root_y} C {root_x} {(root_y + cont_y)/2}, {cont_x} {(root_y + cont_y)/2}, {cont_x} {cont_y}" stroke="#999" stroke-width="3" fill="none" stroke-opacity="0.6"/>')
        svg_parts.append(f'<path d="M {root_x} {root_y} C {root_x} {(root_y + occ_y)/2}, {occ_x} {(root_y + occ_y)/2}, {occ_x} {occ_y}" stroke="#999" stroke-width="3" fill="none" stroke-opacity="0.6"/>')

        # Draw Continuant
        draw_continuant_subtree(continuant, cont_x, cont_y)

        # Draw Occurrent
        draw_occurrent_subtree(occurrent, occ_x, occ_y)

    svg_parts.append('</svg>')

    return '\n'.join(svg_parts)

def draw_continuant_subtree(node, x, y):
    """Draw the Continuant subtree with custom layout"""
    svg_parts = []
    color = colors.get(node.get('type', 'continuant'), '#4299e1')

    # Draw main Continuant node
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="10" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 15}" y="{y + 5}" font-size="14" font-weight="bold" font-family="Arial, sans-serif" fill="#333">{node["label"]}</text>')

    if 'children' in node:
        child_y = y + 50

        # Independent Continuant (main left branch)
        ind_cont = node['children'][0]
        ind_x = x - 150
        draw_independent_continuant(ind_cont, ind_x, child_y, x, y)

        # Specifically Dependent Continuant (middle branch)
        spec_dep = node['children'][1]
        spec_x = x + 50
        draw_specifically_dependent(spec_dep, spec_x, child_y, x, y)

        # Generically Dependent Continuant (right branch)
        gen_dep = node['children'][2]
        gen_x = x + 250
        draw_simple_node(gen_dep, gen_x, child_y, x, y)

    return svg_parts

def draw_independent_continuant(node, x, y, px, py):
    """Draw Independent Continuant branch"""
    color = colors.get(node.get('type', 'continuant'), '#4299e1')

    # Connection
    svg_parts.append(f'<path d="M {px} {py} C {px} {(py + y)/2}, {x} {(py + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')

    # Node
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="8" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 12}" y="{y + 4}" font-size="12" font-family="Arial, sans-serif" fill="#333">{node["label"]}</text>')

    if 'children' in node:
        child_y = y + 45

        # Material Entity
        mat_x = x - 100
        draw_material_entity(node['children'][0], mat_x, child_y, x, y)

        # Immaterial Entity
        imm_x = x
        draw_immaterial_entity(node['children'][1], imm_x, child_y, x, y)

        # Spatial Region
        spat_x = x + 100
        draw_spatial_region(node['children'][2], spat_x, child_y, x, y)

def draw_material_entity(node, x, y, px, py):
    """Draw Material Entity branch"""
    color = colors['material']

    svg_parts.append(f'<path d="M {px} {py} C {px} {(py + y)/2}, {x} {(py + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="8" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 12}" y="{y + 4}" font-size="11" font-family="Arial, sans-serif" fill="#333">{node["label"]}</text>')

    if 'children' in node:
        for i, child in enumerate(node['children']):
            child_x = x - 40 + i * 40
            child_y = y + 40
            draw_simple_node(child, child_x, child_y, x, y)

def draw_immaterial_entity(node, x, y, px, py):
    """Draw Immaterial Entity branch"""
    color = colors['immaterial']

    svg_parts.append(f'<path d="M {px} {py} C {px} {(py + y)/2}, {x} {(py + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="8" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 12}" y="{y + 4}" font-size="11" font-family="Arial, sans-serif" fill="#333">{node["label"]}</text>')

    if 'children' in node:
        child_y = y + 40
        # Site
        draw_simple_node(node['children'][0], x - 40, child_y, x, y)
        # Continuant Fiat Boundary
        draw_boundaries(node['children'][1], x + 40, child_y, x, y)

def draw_boundaries(node, x, y, px, py):
    """Draw Continuant Fiat Boundary"""
    color = colors['immaterial']

    svg_parts.append(f'<path d="M {px} {py} C {px} {(py + y)/2}, {x} {(py + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="7" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 10}" y="{y + 3}" font-size="10" font-family="Arial, sans-serif" fill="#333">CF Boundary</text>')

    if 'children' in node:
        child_y = y + 35
        for i, child in enumerate(node['children']):
            child_x = x - 30 + i * 30
            draw_simple_node(child, child_x, child_y, x, y, font_size=9)

def draw_spatial_region(node, x, y, px, py):
    """Draw Spatial Region branch"""
    color = colors['region']

    svg_parts.append(f'<path d="M {px} {py} C {px} {(py + y)/2}, {x} {(py + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="8" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 12}" y="{y + 4}" font-size="11" font-family="Arial, sans-serif" fill="#333">{node["label"]}</text>')

    if 'children' in node:
        child_y = y + 35
        for i, child in enumerate(node['children']):
            child_x = x - 45 + i * 30
            draw_simple_node(child, child_x, child_y, x, y, font_size=9)

def draw_specifically_dependent(node, x, y, px, py):
    """Draw Specifically Dependent Continuant"""
    color = colors.get(node.get('type', 'continuant'), '#4299e1')

    svg_parts.append(f'<path d="M {px} {py} C {px} {(py + y)/2}, {x} {(py + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="8" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 12}" y="{y + 4}" font-size="11" font-family="Arial, sans-serif" fill="#333">Spec. Dep. Cont.</text>')

    if 'children' in node:
        child_y = y + 40
        # Quality
        draw_quality(node['children'][0], x - 50, child_y, x, y)
        # Realizable Entity
        draw_realizable(node['children'][1], x + 50, child_y, x, y)

def draw_quality(node, x, y, px, py):
    """Draw Quality branch"""
    color = colors['quality']

    svg_parts.append(f'<path d="M {px} {py} C {px} {(py + y)/2}, {x} {(py + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="8" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 12}" y="{y + 4}" font-size="11" font-family="Arial, sans-serif" fill="#333">{node["label"]}</text>')

    if 'children' in node:
        draw_simple_node(node['children'][0], x, y + 35, x, y, font_size=10)

def draw_realizable(node, x, y, px, py):
    """Draw Realizable Entity branch"""
    color = colors['realizable']

    svg_parts.append(f'<path d="M {px} {py} C {px} {(py + y)/2}, {x} {(py + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="8" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 12}" y="{y + 4}" font-size="11" font-family="Arial, sans-serif" fill="#333">{node["label"]}</text>')

    if 'children' in node:
        child_y = y + 35
        # Disposition
        disp_node = node['children'][0]
        draw_disposition(disp_node, x - 30, child_y, x, y)
        # Role
        draw_simple_node(node['children'][1], x + 30, child_y, x, y, font_size=10)

def draw_disposition(node, x, y, px, py):
    """Draw Disposition branch"""
    color = colors['realizable']

    svg_parts.append(f'<path d="M {px} {py} C {px} {(py + y)/2}, {x} {(py + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="7" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 10}" y="{y + 3}" font-size="10" font-family="Arial, sans-serif" fill="#333">{node["label"]}</text>')

    if 'children' in node:
        draw_simple_node(node['children'][0], x, y + 35, x, y, font_size=9)

def draw_occurrent_subtree(node, x, y):
    """Draw the Occurrent subtree"""
    color = colors['occurrent']

    # Draw main Occurrent node
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="10" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 15}" y="{y + 5}" font-size="14" font-weight="bold" font-family="Arial, sans-serif" fill="#333">{node["label"]}</text>')

    if 'children' in node:
        child_y = y + 50

        # Process
        proc_x = x - 100
        draw_process(node['children'][0], proc_x, child_y, x, y)

        # Temporal Region
        temp_x = x
        draw_temporal_region(node['children'][1], temp_x, child_y, x, y)

        # Spatiotemporal Region
        sptemp_x = x + 100
        draw_simple_node(node['children'][2], sptemp_x, child_y, x, y)

def draw_process(node, x, y, px, py):
    """Draw Process branch"""
    color = colors['process']

    svg_parts.append(f'<path d="M {px} {py} C {px} {(py + y)/2}, {x} {(py + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="8" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 12}" y="{y + 4}" font-size="12" font-family="Arial, sans-serif" fill="#333">{node["label"]}</text>')

    if 'children' in node:
        child_y = y + 40
        for i, child in enumerate(node['children']):
            child_x = x - 40 + i * 40
            draw_simple_node(child, child_x, child_y, x, y, font_size=10)

def draw_temporal_region(node, x, y, px, py):
    """Draw Temporal Region branch"""
    color = colors['occurrent']

    svg_parts.append(f'<path d="M {px} {py} C {px} {(py + y)/2}, {x} {(py + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="8" fill="{color}" stroke="#333" stroke-width="2"/>')
    svg_parts.append(f'<text x="{x + 12}" y="{y + 4}" font-size="11" font-family="Arial, sans-serif" fill="#333">{node["label"]}</text>')

    if 'children' in node:
        child_y = y + 35
        for i, child in enumerate(node['children']):
            child_x = x - 30 + i * 60
            draw_simple_node(child, child_x, child_y, x, y, font_size=9)

def draw_simple_node(node, x, y, px, py, font_size=11):
    """Draw a simple leaf node"""
    color = colors.get(node.get('type', 'continuant'), '#999')

    svg_parts.append(f'<path d="M {px} {py} C {px} {(py + y)/2}, {x} {(py + y)/2}, {x} {y}" stroke="#999" stroke-width="2" fill="none" stroke-opacity="0.6"/>')
    svg_parts.append(f'<circle cx="{x}" cy="{y}" r="6" fill="{color}" stroke="#333" stroke-width="2"/>')

    # Shorten long labels
    label = node["label"]
    if len(label) > 20:
        label = label[:17] + "..."

    svg_parts.append(f'<text x="{x + 10}" y="{y + 3}" font-size="{font_size}" font-family="Arial, sans-serif" fill="#333">{label}</text>')

# Generate and save
if __name__ == "__main__":
    svg_content = generate_svg_tree()

    output_file = "/home/user/bfo/docs/bfo-hierarchy-static.svg"
    with open(output_file, 'w') as f:
        f.write(svg_content)

    print(f"✓ Static SVG visualization saved to {output_file}")
