"""
Integration tests for the test generator compute units.
These tests verify the test generation pipeline works correctly.
"""

import pytest
from pathlib import Path


class TestTestGenerator:
    """Test the test generator compute units."""

    def test_load_blueprint(self):
        """Test loading a blueprint."""
        from utils.test_generator.src.test_compute import load_blueprint

        result = load_blueprint({
            'path': 'workflows/logic_vulnerability_pointer/components/fix_gen.json'
        })

        assert result['error'] is None
        assert result['blueprint'] is not None
        assert result['blueprint']['id'] == 'lvp_fix_gen'

    def test_load_blueprint_not_found(self):
        """Test loading a non-existent blueprint."""
        from utils.test_generator.src.test_compute import load_blueprint

        result = load_blueprint({'path': 'nonexistent.json'})

        assert result['error'] is not None
        assert result['blueprint'] is None

    def test_build_graph(self):
        """Test building graph from blueprint."""
        from utils.test_generator.src.test_compute import load_blueprint, build_graph

        bp = load_blueprint({
            'path': 'workflows/logic_vulnerability_pointer/components/fix_gen.json'
        })['blueprint']

        result = build_graph({'blueprint': bp})

        assert result['graph'] is not None
        assert 'adjacency' in result['graph']
        assert 'entry' in result['graph']
        assert result['graph']['entry'] == 'idle'

    def test_analyze_paths(self):
        """Test path analysis."""
        from utils.test_generator.src.test_compute import (
            load_blueprint, build_graph, analyze_paths
        )

        bp = load_blueprint({
            'path': 'workflows/logic_vulnerability_pointer/components/fix_gen.json'
        })['blueprint']
        graph = build_graph({'blueprint': bp})['graph']

        result = analyze_paths({'blueprint': bp, 'graph': graph})

        assert 'paths' in result
        assert len(result['paths']) > 0
        # Should find paths to terminal states
        terminals = {'verified', 'unverified', 'error'}
        final_states = {p['states'][-1] for p in result['paths'] if p['states']}
        assert terminals.issubset(final_states)

    def test_analyze_gates(self):
        """Test gate analysis."""
        from utils.test_generator.src.test_compute import load_blueprint, analyze_gates

        bp = load_blueprint({
            'path': 'workflows/logic_vulnerability_pointer/components/fix_gen.json'
        })['blueprint']

        result = analyze_gates({'blueprint': bp})

        assert 'analysis' in result
        assert 'has_counter_examples' in result['analysis']
        assert 'has_patches' in result['analysis']

    def test_generate_path_tests(self):
        """Test path test generation."""
        from utils.test_generator.src.test_compute import (
            load_blueprint, build_graph, analyze_paths, generate_path_tests
        )

        bp = load_blueprint({
            'path': 'workflows/logic_vulnerability_pointer/components/fix_gen.json'
        })['blueprint']
        graph = build_graph({'blueprint': bp})['graph']
        paths = analyze_paths({'blueprint': bp, 'graph': graph})['paths']

        result = generate_path_tests({'blueprint': bp, 'paths': paths})

        assert 'tests' in result
        assert len(result['tests']) > 0
        for test in result['tests']:
            assert test['type'] == 'path_coverage'
            assert 'events' in test

    def test_generate_contract_tests(self):
        """Test contract test generation."""
        from utils.test_generator.src.test_compute import (
            load_blueprint, build_graph, generate_contract_tests
        )

        bp = load_blueprint({
            'path': 'workflows/logic_vulnerability_pointer/components/fix_gen.json'
        })['blueprint']
        graphResult = build_graph({'blueprint': bp})

        result = generate_contract_tests({'blueprint': bp, 'graph': graphResult})

        assert 'tests' in result
        assert len(result['tests']) > 0

        # Check contract_output tests
        output_tests = [t for t in result['tests'] if t['type'] == 'contract_output']
        assert len(output_tests) > 0
        for test in output_tests:
            assert 'contract_checks' in test
            assert len(test['contract_checks']) > 0

        # Check contract_invariant tests
        invariant_tests = [t for t in result['tests'] if t['type'] == 'contract_invariant']
        assert len(invariant_tests) > 0
        for test in invariant_tests:
            assert 'invariant' in test

    def test_combine_tests(self):
        """Test combining all test types."""
        from utils.test_generator.src.test_compute import (
            load_blueprint, build_graph, analyze_paths, analyze_gates,
            generate_path_tests, generate_state_tests, generate_gate_tests,
            generate_negative_tests, generate_property_tests, generate_contract_tests,
            combine_tests
        )

        bp = load_blueprint({
            'path': 'workflows/logic_vulnerability_pointer/components/fix_gen.json'
        })['blueprint']
        graphResult = build_graph({'blueprint': bp})
        graph = graphResult['graph']
        paths = analyze_paths({'blueprint': bp, 'graph': graph})['paths']
        gateAnalysis = analyze_gates({'blueprint': bp})['analysis']

        result = combine_tests({
            'blueprint': bp,
            'path_tests': generate_path_tests({'blueprint': bp, 'paths': paths})['tests'],
            'state_tests': generate_state_tests({'blueprint': bp, 'paths': paths})['tests'],
            'gate_tests': generate_gate_tests({'blueprint': bp, 'gate_analysis': gateAnalysis})['tests'],
            'negative_tests': generate_negative_tests({'blueprint': bp, 'graph': graph})['tests'],
            'property_tests': generate_property_tests({'blueprint': bp})['tests'],
            'contract_tests': generate_contract_tests({'blueprint': bp, 'graph': graphResult})['tests']
        })

        assert 'tests' in result
        assert 'coverage' in result

        coverage = result['coverage']
        assert coverage['state_coverage']['percentage'] == 100.0
        assert coverage['transition_coverage']['percentage'] == 100.0
        assert coverage['by_type']['contract'] > 0

    def test_format_pytest(self):
        """Test pytest format output."""
        from utils.test_generator.src.test_compute import (
            load_blueprint, build_graph, generate_contract_tests, format_pytest
        )

        bp = load_blueprint({
            'path': 'workflows/logic_vulnerability_pointer/components/fix_gen.json'
        })['blueprint']
        graphResult = build_graph({'blueprint': bp})
        tests = generate_contract_tests({'blueprint': bp, 'graph': graphResult})['tests']

        result = format_pytest({'blueprint': bp, 'tests': tests})

        assert 'output' in result
        output = result['output']
        assert 'import pytest' in output
        assert 'def test_' in output
        assert 'assert' in output
        # Check contract assertions are generated
        assert 'is not None' in output


class TestBlueprintCoverage:
    """Test blueprint coverage metrics."""

    def test_all_components_100_state_coverage(self):
        """Verify all components have 100% state coverage."""
        from utils.test_generator.src.test_compute import (
            load_blueprint, build_graph, analyze_paths,
            generate_path_tests, generate_state_tests, combine_tests
        )

        components = [
            'workflows/logic_vulnerability_pointer/components/fix_gen.json',
            'workflows/logic_vulnerability_pointer/components/xray.json',
            'workflows/python_to_lpp/components/scanner.json',
        ]

        for comp_path in components:
            bp = load_blueprint({'path': comp_path})['blueprint']
            graph = build_graph({'blueprint': bp})['graph']
            paths = analyze_paths({'blueprint': bp, 'graph': graph})['paths']

            result = combine_tests({
                'blueprint': bp,
                'path_tests': generate_path_tests({'blueprint': bp, 'paths': paths})['tests'],
                'state_tests': generate_state_tests({'blueprint': bp, 'paths': paths})['tests'],
                'gate_tests': [],
                'negative_tests': [],
                'property_tests': [],
                'contract_tests': []
            })

            coverage = result['coverage']
            assert coverage['state_coverage']['percentage'] == 100.0, \
                f"{comp_path} has {coverage['state_coverage']['percentage']}% state coverage"
            assert coverage['transition_coverage']['percentage'] == 100.0, \
                f"{comp_path} has {coverage['transition_coverage']['percentage']}% transition coverage"
