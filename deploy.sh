#!/bin/bash
# L++ Documentation Deployment Script
# Generates all documentation artifacts for any L++ project
#
# Can be used on:
# 1. The L++ framework itself (default)
# 2. Any external L++ project via --project flag

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DOC_GENERATOR="${SCRIPT_DIR}/utils/doc_generator/interactive.py"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Default project path (empty = L++ utils)
PROJECT_PATH=""
PROJECT_FLAG=""

print_header() {
    echo -e "${BLUE}╔══════════════════════════════════════════════════════════╗${NC}"
    echo -e "${BLUE}║          L++ Documentation Deployment                    ║${NC}"
    echo -e "${BLUE}╚══════════════════════════════════════════════════════════╝${NC}"
}

print_usage() {
    echo "Usage: ./deploy.sh [options] [command]"
    echo ""
    echo "Commands:"
    echo "  docs      Generate all documentation (default)"
    echo "  graphs    Generate only HTML graph visualizations"
    echo "  logic     Generate only logic flow graphs from Python"
    echo "  functions Generate only function dependency graphs"
    echo "  mermaid   Generate only Mermaid diagrams"
    echo "  readme    Update only README files"
    echo "  dashboard Generate only dashboard"
    echo "  report    Generate only analysis report"
    echo "  clean     Remove all generated artifacts"
    echo "  validate  Validate all blueprints with TLA+"
    echo ""
    echo "Options:"
    echo "  -p, --project <path>  Path to L++ project (default: L++ utils)"
    echo "  -q, --quiet           Suppress verbose output"
    echo "  -h, --help            Show this help message"
    echo ""
    echo "Examples:"
    echo "  ./deploy.sh                           # Generate docs for L++ utils"
    echo "  ./deploy.sh -p /my/app docs           # Generate docs for external project"
    echo "  ./deploy.sh --project /my/app mermaid # Generate Mermaid for external project"
    echo "  ./deploy.sh clean                     # Remove generated files"
}

generate_docs() {
    local flags="$1"
    echo -e "${GREEN}Generating documentation...${NC}"
    python3 "${DOC_GENERATOR}" ${PROJECT_FLAG} ${flags}
}

clean_artifacts() {
    local target_dir="${PROJECT_PATH:-${SCRIPT_DIR}/utils}"
    echo -e "${YELLOW}Cleaning generated artifacts in ${target_dir}...${NC}"

    # Remove results directories content (but keep the directories)
    find "${target_dir}" -type d -name "results" -exec sh -c 'rm -f "$1"/*.html "$1"/*.mmd 2>/dev/null || true' _ {} \;

    # Remove generated dashboard
    rm -f "${target_dir}/dashboard.html"

    # Remove analysis report
    rm -f "${target_dir}/analysis_report.md"

    echo -e "${GREEN}Cleaned generated artifacts${NC}"
}

validate_blueprints() {
    local target_dir="${PROJECT_PATH:-${SCRIPT_DIR}/utils}"
    echo -e "${GREEN}Validating blueprints in ${target_dir}...${NC}"

    if ! command -v tla2sany &> /dev/null; then
        echo -e "${RED}Error: TLA+ tools not found. Install TLA+ toolbox.${NC}"
        exit 1
    fi

    find "${target_dir}" -name "*.json" -type f | while read -r bp; do
        # Skip non-blueprint files
        if ! grep -q '"states"' "$bp" 2>/dev/null; then
            continue
        fi
        name=$(basename "$bp" .json)
        dir=$(dirname "$bp")
        tla_file="${dir}/tla/${name}.tla"

        if [ -f "$tla_file" ]; then
            echo "  Validating: $name"
            tla2sany "$tla_file" 2>/dev/null || echo -e "${RED}  Failed: $name${NC}"
        fi
    done
}

# Parse options first
while [[ $# -gt 0 ]]; do
    case "$1" in
        -p|--project)
            PROJECT_PATH="$2"
            PROJECT_FLAG="--project $2"
            shift 2
            ;;
        -q|--quiet)
            PROJECT_FLAG="${PROJECT_FLAG} --quiet"
            shift
            ;;
        -h|--help|help)
            print_header
            print_usage
            exit 0
            ;;
        -*)
            echo -e "${RED}Unknown option: $1${NC}"
            print_usage
            exit 1
            ;;
        *)
            break
            ;;
    esac
done

# Main
print_header

if [ -n "$PROJECT_PATH" ]; then
    echo -e "${BLUE}Project: ${PROJECT_PATH}${NC}"
fi

COMMAND="${1:-docs}"

case "$COMMAND" in
    docs|all)
        generate_docs "--all"
        ;;
    graphs)
        generate_docs "--graphs"
        ;;
    logic)
        generate_docs "--logic"
        ;;
    functions)
        generate_docs "--functions"
        ;;
    mermaid)
        generate_docs "--mermaid"
        ;;
    readme)
        generate_docs "--readme"
        ;;
    dashboard)
        generate_docs "--dashboard"
        ;;
    report)
        generate_docs "--report"
        ;;
    clean)
        clean_artifacts
        ;;
    validate)
        validate_blueprints
        ;;
    *)
        echo -e "${RED}Unknown command: $COMMAND${NC}"
        print_usage
        exit 1
        ;;
esac

echo -e "\n${GREEN}Done!${NC}"
