#!/bin/bash
# Setup script for BFO project development

set -e

echo "Setting up BFO development environment..."

# Check if Python is installed
if ! command -v python3 &> /dev/null; then
    echo "Error: Python 3 is not installed"
    exit 1
fi

# Install dependencies
echo "Installing Python dependencies..."
pip install -r requirements.txt

# Setup pre-commit hooks
echo "Setting up pre-commit hooks..."
pre-commit install

# Run initial validation
echo "Running initial validation..."
cd bfo-project
python bfo_z3_validation.py
python bfo_validation_demo.py
cd ..

# Generate visualization files
echo "Generating visualization files..."
python bfo-project/extract_hierarchy.py
python bfo-project/create_preview_image.py

echo ""
echo "Setup complete!"
echo ""
echo "Pre-commit hooks are now installed. They will run automatically before each commit."
echo "To manually run all hooks: pre-commit run --all-files"
echo ""
echo "To run validation manually:"
echo "  cd bfo-project && python bfo_z3_validation.py"
echo ""
