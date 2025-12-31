#!/usr/bin/env python3
"""
L++ (Logic Plus Plus) - The Universal Deterministic Logic Workflow Machine

Install with: pip install -e .
"""

from setuptools import setup, find_packages
from pathlib import Path

HERE = Path(__file__).parent
README = (HERE / "README.md").read_text(encoding="utf-8")

# Extract version from package
VERSION = "1.0.0"

setup(
    name="lpp",
    version=VERSION,
    author="L++ Team",
    author_email="lpp@example.com",
    description="The Universal Deterministic Logic Workflow Machine",
    long_description=README,
    long_description_content_type="text/markdown",
    url="https://github.com/lpp-project/lpp",
    license="MIT",
    
    # Package configuration
    package_dir={"": "src"},
    packages=find_packages(where="src"),
    
    # Include non-Python files
    include_package_data=True,
    package_data={
        "blueprints": ["*.json", "**/*.json"],
        "frame_py": ["tlaps_seals/*.json"],
    },
    
    # Python version requirement
    python_requires=">=3.9",
    
    # Dependencies (L++ core uses only stdlib)
    install_requires=[
        # Core has no external dependencies - stdlib only
    ],
    
    # Optional dependencies for extended features
    extras_require={
        "dev": [
            "pytest>=7.0",
            "pytest-cov>=4.0",
            "black>=23.0",
            "mypy>=1.0",
            "ruff>=0.1.0",
        ],
        "llm": [
            "openai>=1.0",
        ],
        "all": [
            "openai>=1.0",
            "pytest>=7.0",
        ],
    },
    
    # Entry points for CLI tools
    entry_points={
        "console_scripts": [
            "lpp-compile=frame_py.compiler:main",
            "lpp-visualize=frame_py.visualizer:main",
        ],
    },
    
    # Classifiers
    classifiers=[
        "Development Status :: 4 - Beta",
        "Intended Audience :: Developers",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Programming Language :: Python :: 3.12",
        "Topic :: Software Development :: Libraries :: Python Modules",
        "Topic :: Software Development :: Code Generators",
        "Topic :: Software Development :: Compilers",
    ],
    
    # Keywords for PyPI
    keywords=[
        "state-machine",
        "workflow",
        "logic",
        "deterministic",
        "blueprint",
        "compiler",
        "fsm",
        "business-logic",
    ],
)
