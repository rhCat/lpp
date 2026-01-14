"""
Pytest configuration for L++ tests.

Handles auto-generated tests with incomplete fixtures.
"""

import pytest


def pytest_collection_modifyitems(config, items):
    """Skip generated blueprint tests that have unimplemented fixtures."""
    skip_marker = pytest.mark.skip(
        reason="Generated test with placeholder operator fixture"
    )

    for item in items:
        # Skip generated blueprint tests that use operator fixture
        if 'generated' in str(item.fspath) and 'operator' in item.fixturenames:
            item.add_marker(skip_marker)
