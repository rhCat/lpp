"""Auto-generated tests for policy_generator_compute.py"""
import pytest
import sys
sys.path.insert(0, str('/Users/ruihe/mnt/lpp/lpp/utils/policy_generator/src'))
from policy_generator_compute import COMPUTE_REGISTRY

def test_registry_exists():
    assert COMPUTE_REGISTRY is not None
    assert len(COMPUTE_REGISTRY) > 0

def test_all_functions_callable():
    for name, func in COMPUTE_REGISTRY.items():
        assert callable(func), f"{name} is not callable"
