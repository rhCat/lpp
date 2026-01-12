#!/bin/bash
# L++ Comprehensive Test Runner
# Runs both Blueprint (infrastructure) and Python (feature) coverage tests
#
# Usage:
#   ./test_all.sh              # Run all tests with coverage
#   ./test_all.sh generate     # Generate tests for all blueprints
#   ./test_all.sh blueprint    # Run only blueprint tests
#   ./test_all.sh compute      # Run only compute/Python tests
#   ./test_all.sh report       # Show coverage report

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_GEN="${SCRIPT_DIR}/utils/test_generator/comprehensive_test.py"
GENERATED_DIR="${SCRIPT_DIR}/tests/generated"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

print_header() {
    echo -e "${BLUE}╔══════════════════════════════════════════════════════════╗${NC}"
    echo -e "${BLUE}║          L++ Comprehensive Test Suite                    ║${NC}"
    echo -e "${BLUE}║   Blueprint (Infrastructure) + Python (Features)         ║${NC}"
    echo -e "${BLUE}╚══════════════════════════════════════════════════════════╝${NC}"
}

print_usage() {
    echo "Usage: ./test_all.sh [command]"
    echo ""
    echo "Commands:"
    echo "  all       Run all tests with full coverage (default)"
    echo "  generate  Generate tests for all blueprints"
    echo "  blueprint Run only blueprint/infrastructure tests"
    echo "  compute   Run only compute/feature tests"
    echo "  report    Show combined coverage report"
    echo "  clean     Remove generated test files"
    echo ""
    echo "Coverage Types:"
    echo "  - Blueprint Coverage: State, transition, gate, contract coverage"
    echo "  - Python Coverage: Line, branch coverage of compute functions"
}

generate_tests() {
    echo -e "${GREEN}Generating comprehensive tests...${NC}"
    echo ""

    python3 "${TEST_GEN}" --all --workflow-dir "${SCRIPT_DIR}/workflows" --output-dir "${GENERATED_DIR}"

    echo ""
    echo -e "${GREEN}Tests generated in: ${GENERATED_DIR}${NC}"

    # Count generated files
    bp_tests=$(find "${GENERATED_DIR}" -name "*_blueprint.py" 2>/dev/null | wc -l | tr -d ' ')
    compute_tests=$(find "${GENERATED_DIR}" -name "*_compute.py" 2>/dev/null | wc -l | tr -d ' ')

    echo -e "  Blueprint tests: ${CYAN}${bp_tests}${NC} files"
    echo -e "  Compute tests:   ${CYAN}${compute_tests}${NC} files"
}

run_all_tests() {
    echo -e "${GREEN}Running comprehensive test suite...${NC}"
    echo ""

    # Check if tests exist
    if [ ! -d "${GENERATED_DIR}" ] || [ -z "$(ls -A ${GENERATED_DIR}/*.py 2>/dev/null)" ]; then
        echo -e "${YELLOW}No generated tests found. Generating...${NC}"
        generate_tests
        echo ""
    fi

    echo -e "${CYAN}=== Running All Tests with Coverage ===${NC}"
    echo ""

    # Run pytest with coverage
    python3 -m pytest "${SCRIPT_DIR}/tests" \
        --cov=src \
        --cov=utils \
        --cov-report=term-missing \
        --cov-report=html:htmlcov \
        --cov-report=json:coverage.json \
        -v \
        --tb=short

    echo ""
    echo -e "${GREEN}Coverage report: htmlcov/index.html${NC}"
}

run_blueprint_tests() {
    echo -e "${GREEN}Running blueprint (infrastructure) tests...${NC}"
    echo ""

    python3 -m pytest "${GENERATED_DIR}" \
        -k "blueprint" \
        --cov=src \
        --cov=utils \
        --cov-report=term-missing \
        -v \
        --tb=short
}

run_compute_tests() {
    echo -e "${GREEN}Running compute (feature) tests...${NC}"
    echo ""

    # Run compute-specific tests
    python3 -m pytest "${GENERATED_DIR}" \
        -k "compute" \
        --cov=src \
        --cov=utils \
        --cov-report=term-missing \
        -v \
        --tb=short
}

show_coverage_report() {
    echo -e "${GREEN}Coverage Report${NC}"
    echo ""

    if [ -f "${SCRIPT_DIR}/coverage.json" ]; then
        echo -e "${CYAN}=== Python Coverage Summary ===${NC}"
        python3 -c "
import json
with open('coverage.json') as f:
    data = json.load(f)
    totals = data.get('totals', {})
    print(f\"  Lines:     {totals.get('covered_lines', 0)}/{totals.get('num_statements', 0)} ({totals.get('percent_covered', 0):.1f}%)\")
    print(f\"  Branches:  {totals.get('covered_branches', 0)}/{totals.get('num_branches', 0)}\")
    print(f\"  Missing:   {totals.get('missing_lines', 0)} lines\")
"
    else
        echo -e "${YELLOW}No coverage.json found. Run tests first.${NC}"
    fi

    echo ""
    echo -e "${CYAN}=== Blueprint Coverage Summary ===${NC}"

    # Parse blueprint test summaries
    for summary in "${GENERATED_DIR}"/*_test_summary.json; do
        if [ -f "$summary" ]; then
            python3 -c "
import json
import sys
with open('${summary}') as f:
    data = json.load(f)
    bp_id = data.get('blueprint_id', 'unknown')
    bp_cov = data.get('blueprint_tests', {}).get('coverage', {})
    state_cov = bp_cov.get('state_coverage', {})
    trans_cov = bp_cov.get('transition_coverage', {})
    print(f\"  {bp_id}:\")
    print(f\"    States:      {state_cov.get('covered', 0)}/{state_cov.get('total', 0)} ({state_cov.get('percentage', 0):.0f}%)\")
    print(f\"    Transitions: {trans_cov.get('covered', 0)}/{trans_cov.get('total', 0)} ({trans_cov.get('percentage', 0):.0f}%)\")
"
        fi
    done 2>/dev/null || echo -e "${YELLOW}No blueprint summaries found.${NC}"
}

clean_generated() {
    echo -e "${YELLOW}Cleaning generated test files...${NC}"
    rm -rf "${GENERATED_DIR}"
    rm -f "${SCRIPT_DIR}/coverage.json"
    rm -rf "${SCRIPT_DIR}/htmlcov"
    rm -rf "${SCRIPT_DIR}/.coverage"
    echo -e "${GREEN}Cleaned.${NC}"
}

# Main
print_header
echo ""

COMMAND="${1:-all}"

case "$COMMAND" in
    all)
        run_all_tests
        ;;
    generate)
        generate_tests
        ;;
    blueprint)
        run_blueprint_tests
        ;;
    compute)
        run_compute_tests
        ;;
    report)
        show_coverage_report
        ;;
    clean)
        clean_generated
        ;;
    -h|--help|help)
        print_usage
        ;;
    *)
        echo -e "${RED}Unknown command: $COMMAND${NC}"
        print_usage
        exit 1
        ;;
esac

echo ""
echo -e "${GREEN}Done!${NC}"
