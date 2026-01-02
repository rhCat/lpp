#!/bin/bash
# L++ UV Environment Setup Script
# Handles mounted filesystem limitations by creating venv in local storage

set -e

PROJECT_DIR="$(cd "$(dirname "$0")" && pwd)"
VENV_DIR="${LPP_VENV_DIR:-/tmp/lpp_venv}"

echo "L++ UV Environment Setup"
echo "========================"
echo "Project: $PROJECT_DIR"
echo "Venv:    $VENV_DIR"
echo ""

# Check uv is installed
if ! command -v uv &> /dev/null; then
    echo "Installing uv..."
    curl -LsSf https://astral.sh/uv/install.sh | sh
fi

# Create/recreate venv
if [ "$1" = "--clean" ] || [ ! -d "$VENV_DIR" ]; then
    echo "Creating virtual environment..."
    rm -rf "$VENV_DIR"
    UV_LINK_MODE=copy uv venv "$VENV_DIR" --python 3.12
fi

# Install package
echo "Installing lpp with all extras..."
cd "$PROJECT_DIR"
UV_LINK_MODE=copy uv pip install -e ".[all]" --python "$VENV_DIR/bin/python"

echo ""
echo "✓ Environment ready!"
echo ""
echo "To activate:"
echo "  source $VENV_DIR/bin/activate"
echo ""
echo "Or use directly:"
echo "  $VENV_DIR/bin/python -c 'import frame_py; print(frame_py.__version__)'"
