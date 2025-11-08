#!/usr/bin/env python3
"""
Create a simple preview image for the BFO hierarchy
Using matplotlib to generate a preview diagram
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch, Circle, FancyArrowPatch
import json

# Set up the figure
fig, ax = plt.subplots(1, 1, figsize=(16, 12))
ax.set_xlim(0, 16)
ax.set_ylim(0, 12)
ax.axis('off')

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

# Title
ax.text(8, 11.5, 'BFO (Basic Formal Ontology) Hierarchy',
        ha='center', va='top', fontsize=24, fontweight='bold', color='#333')
ax.text(8, 11, '35 Classes • 51 FOL Axioms • Z3 Validated',
        ha='center', va='top', fontsize=14, color='#666')

# Add legend
legend_y = 10.5
legend_elements = [
    ('Continuant', colors['continuant']),
    ('Occurrent', colors['occurrent']),
    ('Material', colors['material']),
    ('Quality/Realizable', colors['quality']),
    ('Process', colors['process'])
]

for i, (label, color) in enumerate(legend_elements):
    x = 2 + i * 2.5
    circle = Circle((x, legend_y), 0.12, color=color, ec='#333', linewidth=2)
    ax.add_patch(circle)
    ax.text(x + 0.2, legend_y, label, va='center', fontsize=10, color='#666')

def draw_box(x, y, width, height, text, color, fontsize=9):
    """Draw a rounded box with text"""
    box = FancyBboxPatch((x - width/2, y - height/2), width, height,
                         boxstyle="round,pad=0.05",
                         facecolor=color, edgecolor='#333', linewidth=2)
    ax.add_patch(box)
    ax.text(x, y, text, ha='center', va='center',
            fontsize=fontsize, fontweight='bold', color='white')

def draw_arrow(x1, y1, x2, y2):
    """Draw an arrow between two points"""
    arrow = FancyArrowPatch((x1, y1), (x2, y2),
                           arrowstyle='-', linewidth=2, color='#999',
                           connectionstyle="arc3,rad=0.1")
    ax.add_patch(arrow)

# Root: Entity
draw_box(8, 9.5, 1.5, 0.4, 'Entity', colors['root'], fontsize=11)

# Main branches
draw_box(4, 8.5, 2, 0.4, 'Continuant', colors['continuant'], fontsize=10)
draw_box(12, 8.5, 2, 0.4, 'Occurrent', colors['occurrent'], fontsize=10)

draw_arrow(8, 9.3, 4, 8.7)
draw_arrow(8, 9.3, 12, 8.7)

# Continuant sub-branches
draw_box(2, 7.3, 1.8, 0.35, 'Independent\nContinuant', colors['continuant'], fontsize=8)
draw_box(4, 7.3, 1.8, 0.35, 'Specifically\nDependent', colors['continuant'], fontsize=8)
draw_box(6, 7.3, 1.8, 0.35, 'Generically\nDependent', colors['continuant'], fontsize=8)

draw_arrow(4, 8.3, 2, 7.5)
draw_arrow(4, 8.3, 4, 7.5)
draw_arrow(4, 8.3, 6, 7.5)

# Independent Continuant children
draw_box(0.8, 6, 1.3, 0.3, 'Material\nEntity', colors['material'], fontsize=7)
draw_box(2, 6, 1.3, 0.3, 'Immaterial\nEntity', colors['immaterial'], fontsize=7)
draw_box(3.2, 6, 1.3, 0.3, 'Spatial\nRegion', colors['region'], fontsize=7)

draw_arrow(2, 7.1, 0.8, 6.15)
draw_arrow(2, 7.1, 2, 6.15)
draw_arrow(2, 7.1, 3.2, 6.15)

# Material Entity children
draw_box(0.3, 5, 0.8, 0.25, 'Object', colors['material'], fontsize=7)
draw_box(0.8, 5, 1, 0.25, 'Fiat Object\nPart', colors['material'], fontsize=6)
draw_box(1.4, 5, 1, 0.25, 'Object\nAggregate', colors['material'], fontsize=6)

draw_arrow(0.8, 5.85, 0.3, 5.12)
draw_arrow(0.8, 5.85, 0.8, 5.12)
draw_arrow(0.8, 5.85, 1.4, 5.12)

# Immaterial Entity children
draw_box(1.7, 5, 0.7, 0.25, 'Site', colors['immaterial'], fontsize=7)
draw_box(2.3, 5, 1.1, 0.25, 'Continuant\nFiat Boundary', colors['immaterial'], fontsize=6)

draw_arrow(2, 5.85, 1.7, 5.12)
draw_arrow(2, 5.85, 2.3, 5.12)

# Fiat Boundary children
draw_box(1.9, 4.2, 0.6, 0.2, '0D', colors['immaterial'], fontsize=6)
draw_box(2.3, 4.2, 0.6, 0.2, '1D', colors['immaterial'], fontsize=6)
draw_box(2.7, 4.2, 0.6, 0.2, '2D', colors['immaterial'], fontsize=6)

draw_arrow(2.3, 4.87, 1.9, 4.3)
draw_arrow(2.3, 4.87, 2.3, 4.3)
draw_arrow(2.3, 4.87, 2.7, 4.3)

# Spatial Region children
draw_box(2.7, 5, 0.7, 0.25, '0D\nSpatial', colors['region'], fontsize=6)
draw_box(3.2, 5, 0.7, 0.25, '1D\nSpatial', colors['region'], fontsize=6)
draw_box(3.7, 5, 0.7, 0.25, '2D\nSpatial', colors['region'], fontsize=6)
draw_box(4.2, 5, 0.7, 0.25, '3D\nSpatial', colors['region'], fontsize=6)

draw_arrow(3.2, 5.85, 2.7, 5.12)
draw_arrow(3.2, 5.85, 3.2, 5.12)
draw_arrow(3.2, 5.85, 3.7, 5.12)
draw_arrow(3.2, 5.85, 4.2, 5.12)

# Specifically Dependent children
draw_box(3.8, 6, 1, 0.3, 'Quality', colors['quality'], fontsize=7)
draw_box(4.7, 6, 1.2, 0.3, 'Realizable\nEntity', colors['realizable'], fontsize=7)

draw_arrow(4, 7.1, 3.8, 6.15)
draw_arrow(4, 7.1, 4.7, 6.15)

# Quality children
draw_box(3.8, 5, 1, 0.25, 'Relational\nQuality', colors['quality'], fontsize=6)
draw_arrow(3.8, 5.85, 3.8, 5.12)

# Realizable Entity children
draw_box(4.3, 5, 1, 0.25, 'Disposition', colors['realizable'], fontsize=6)
draw_box(5.1, 5, 0.8, 0.25, 'Role', colors['realizable'], fontsize=6)

draw_arrow(4.7, 5.85, 4.3, 5.12)
draw_arrow(4.7, 5.85, 5.1, 5.12)

# Disposition children
draw_box(4.3, 4.2, 0.9, 0.2, 'Function', colors['realizable'], fontsize=6)
draw_arrow(4.3, 4.87, 4.3, 4.3)

# Occurrent sub-branches
draw_box(10.5, 7.3, 1.5, 0.35, 'Process', colors['process'], fontsize=8)
draw_box(12, 7.3, 1.5, 0.35, 'Temporal\nRegion', colors['occurrent'], fontsize=8)
draw_box(13.5, 7.3, 1.8, 0.35, 'Spatiotemporal\nRegion', colors['occurrent'], fontsize=8)

draw_arrow(12, 8.3, 10.5, 7.5)
draw_arrow(12, 8.3, 12, 7.5)
draw_arrow(12, 8.3, 13.5, 7.5)

# Process children
draw_box(9.8, 6, 1.2, 0.3, 'Process\nBoundary', colors['process'], fontsize=7)
draw_box(10.5, 6, 1.2, 0.3, 'Process\nProfile', colors['process'], fontsize=7)
draw_box(11.2, 6, 1, 0.3, 'History', colors['process'], fontsize=7)

draw_arrow(10.5, 7.1, 9.8, 6.15)
draw_arrow(10.5, 7.1, 10.5, 6.15)
draw_arrow(10.5, 7.1, 11.2, 6.15)

# Temporal Region children
draw_box(11.6, 6, 1.2, 0.3, '0D\nTemporal', colors['occurrent'], fontsize=7)
draw_box(12.4, 6, 1.2, 0.3, '1D\nTemporal', colors['occurrent'], fontsize=7)

draw_arrow(12, 7.1, 11.6, 6.15)
draw_arrow(12, 7.1, 12.4, 6.15)

# Add annotation
ax.text(8, 0.5, 'Interactive version: Click to expand/collapse • Hover for details • Drag to pan • Scroll to zoom',
        ha='center', va='center', fontsize=10, style='italic', color='#666',
        bbox=dict(boxstyle='round,pad=0.5', facecolor='#f0f0f0', edgecolor='#999'))

plt.tight_layout()
plt.savefig('/home/user/bfo/docs/bfo-hierarchy-preview.png', dpi=200, bbox_inches='tight',
            facecolor='white', edgecolor='none')
print("✓ Preview image saved to /home/user/bfo/docs/bfo-hierarchy-preview.png")

plt.close()
