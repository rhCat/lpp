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
    echo "  tests     Generate comprehensive tests (blueprint + compute)"
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

    # Check for available TLA+ tools
    local TLA2TOOLS_JAR="${HOME}/.local/share/tlaplus/tla2tools.jar"

    if command -v tla2sany &> /dev/null; then
        TLA_CMD="tla2sany"
    elif [ -f "${TLA2TOOLS_JAR}" ]; then
        TLA_CMD="java -cp ${TLA2TOOLS_JAR} tla2sany.SANY"
    else
        echo -e "${RED}Error: TLA+ tools not found.${NC}"
        echo -e "${RED}  Expected: tla2sany command or ${TLA2TOOLS_JAR}${NC}"
        exit 1
    fi
    echo -e "  Using: SANY (TLA+ syntax checker)"

    find "${target_dir}" -name "*.json" -type f | while read -r bp; do
        # Skip non-blueprint files
        if ! grep -q '"states"' "$bp" 2>/dev/null; then
            continue
        fi
        name=$(basename "$bp" .json)
        dir=$(dirname "$bp")
        tla_file="${dir}/tla/${name}.tla"

        if [ -f "$tla_file" ]; then
            echo -n "  Validating: $name ... "
            if ${TLA_CMD} "$tla_file" >/dev/null 2>&1; then
                echo -e "${GREEN}OK${NC}"
            else
                echo -e "${RED}FAILED${NC}"
            fi
        fi
    done
}

generate_tests() {
    local target_dir="${PROJECT_PATH:-${SCRIPT_DIR}/workflows}"
    local output_dir="${PROJECT_PATH:-${SCRIPT_DIR}}/tests/generated"
    echo -e "${GREEN}Generating comprehensive tests...${NC}"
    echo -e "  Source: ${target_dir}"
    echo -e "  Output: ${output_dir}"

    python3 "${SCRIPT_DIR}/utils/test_generator/comprehensive_test.py" \
        --all \
        --workflow-dir "${target_dir}" \
        --output-dir "${output_dir}"

    echo -e "${GREEN}Tests generated successfully${NC}"
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
    tests)
        generate_tests
        ;;
    *)
        echo -e "${RED}Unknown command: $COMMAND${NC}"
        print_usage
        exit 1
        ;;
esac

echo -e "\n${GREEN}Done!${NC}"
