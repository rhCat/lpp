"""
CLI Test Suite for L++ Dev Suite

Tests the main CLI commands and utility invocations.
"""
import pytest
import subprocess
import sys
from pathlib import Path

# Test fixtures
FIXTURES_DIR = Path(__file__).parent / "fixtures"
SAMPLE_BLUEPRINT = Path(__file__).parent.parent / "src/lpp/util/logic_decoder/blueprint.json"
SAMPLE_PYTHON = Path(__file__).parent.parent / "src/lpp/__init__.py"
UTILS_DIR = Path(__file__).parent.parent / "src/lpp/util"


def run_cli(args: list[str], timeout: int = 30) -> subprocess.CompletedProcess:
    """Run lpp CLI command and return result."""
    cmd = [sys.executable, "-m", "lpp.cli"] + args
    return subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        timeout=timeout,
        cwd=Path(__file__).parent.parent
    )


class TestCLIBasic:
    """Test basic CLI commands."""

    def test_version(self):
        """Test version command."""
        result = run_cli(["version"])
        assert result.returncode == 0
        assert "L++ Dev Suite" in result.stdout

    def test_version_flag(self):
        """Test --version flag."""
        result = run_cli(["--version"])
        assert result.returncode == 0
        assert "L++ Dev Suite" in result.stdout

    def test_help_no_args(self):
        """Test help with no arguments."""
        result = run_cli([])
        assert result.returncode == 0
        assert "lpp <command>" in result.stdout

    def test_list_utilities(self):
        """Test list command shows utilities."""
        result = run_cli(["list", "--utils"])
        assert result.returncode == 0
        assert "Utilities:" in result.stdout
        assert "logic_decoder" in result.stdout

    def test_list_workflows(self):
        """Test list command shows workflows."""
        result = run_cli(["list", "--workflows"])
        assert result.returncode == 0
        assert "Workflows:" in result.stdout

    def test_unknown_command(self):
        """Test unknown command returns error."""
        result = run_cli(["unknown_command_xyz"])
        assert result.returncode == 1
        assert "Unknown command" in result.stdout


class TestCLIValidate:
    """Test validate command."""

    def test_validate_valid_blueprint(self):
        """Test validating a valid blueprint."""
        if not SAMPLE_BLUEPRINT.exists():
            pytest.skip("Sample blueprint not found")
        result = run_cli(["validate", str(SAMPLE_BLUEPRINT)])
        assert result.returncode == 0
        assert "passed" in result.stdout.lower()

    def test_validate_missing_file(self):
        """Test validating non-existent file."""
        result = run_cli(["validate", "nonexistent.json"])
        assert result.returncode == 1

    def test_validate_no_args(self):
        """Test validate with no arguments."""
        result = run_cli(["validate"])
        assert result.returncode == 1
        assert "Usage:" in result.stdout


class TestCLICompile:
    """Test compile command."""

    def test_compile_no_args(self):
        """Test compile with no arguments shows usage."""
        result = run_cli(["compile"])
        # Should show usage or error
        assert result.returncode in [0, 1, 2]


class TestCLIDocs:
    """Test docs command."""

    def test_docs_no_args(self):
        """Test docs with no arguments."""
        result = run_cli(["docs"])
        assert result.returncode == 1
        assert "Usage:" in result.stdout


class TestCLIUtil:
    """Test util command for running utilities."""

    def test_util_no_args(self):
        """Test util with no arguments lists utilities."""
        result = run_cli(["util"])
        assert result.returncode == 1
        assert "Available utilities:" in result.stdout

    def test_util_unknown(self):
        """Test util with unknown utility."""
        result = run_cli(["util", "unknown_util_xyz"])
        assert result.returncode == 1
        assert "Unknown utility" in result.stdout

    def test_util_logic_decoder(self):
        """Test logic_decoder utility."""
        if not SAMPLE_PYTHON.exists():
            pytest.skip("Sample Python file not found")
        result = run_cli(["util", "logic_decoder", str(SAMPLE_PYTHON)])
        assert result.returncode == 0
        assert "State: complete" in result.stdout

    def test_util_blueprint_linter(self):
        """Test blueprint_linter utility."""
        if not SAMPLE_BLUEPRINT.exists():
            pytest.skip("Sample blueprint not found")
        result = run_cli(["util", "blueprint_linter", str(SAMPLE_BLUEPRINT)])
        assert result.returncode == 0
        assert "State: complete" in result.stdout

    def test_util_test_generator(self):
        """Test test_generator utility."""
        if not SAMPLE_BLUEPRINT.exists():
            pytest.skip("Sample blueprint not found")
        result = run_cli(["util", "test_generator", str(SAMPLE_BLUEPRINT)])
        assert result.returncode == 0
        assert "State: complete" in result.stdout

    def test_util_function_decoder(self):
        """Test function_decoder utility."""
        if not SAMPLE_PYTHON.exists():
            pytest.skip("Sample Python file not found")
        result = run_cli(["util", "function_decoder", str(SAMPLE_PYTHON)])
        assert result.returncode == 0
        assert "State:" in result.stdout

    def test_util_blueprint_registry(self):
        """Test blueprint_registry utility."""
        if not UTILS_DIR.exists():
            pytest.skip("Utils directory not found")
        result = run_cli(["util", "blueprint_registry", str(UTILS_DIR)])
        assert result.returncode == 0
        assert "State: ready" in result.stdout

    def test_util_event_simulator(self):
        """Test event_simulator utility."""
        if not SAMPLE_BLUEPRINT.exists():
            pytest.skip("Sample blueprint not found")
        result = run_cli(["util", "event_simulator", str(SAMPLE_BLUEPRINT)])
        assert result.returncode == 0
        assert "State: ready" in result.stdout

    def test_util_skill_contractor(self):
        """Test skill_contractor utility (no args)."""
        result = run_cli(["util", "skill_contractor"])
        assert result.returncode == 0
        assert "State: idle" in result.stdout

    def test_util_task_orchestrator(self):
        """Test task_orchestrator utility (no args)."""
        result = run_cli(["util", "task_orchestrator"])
        assert result.returncode == 0
        assert "State: idle" in result.stdout

    def test_util_scholar_chat(self):
        """Test scholar_chat utility."""
        result = run_cli(["util", "scholar_chat", "test query"])
        assert result.returncode == 0
        assert "State: idle" in result.stdout


class TestCLIWorkflow:
    """Test workflow command."""

    def test_workflow_no_args(self):
        """Test workflow with no arguments lists workflows."""
        result = run_cli(["workflow"])
        assert result.returncode == 1
        assert "Available workflows:" in result.stdout

    def test_workflow_unknown(self):
        """Test workflow with unknown workflow."""
        result = run_cli(["workflow", "unknown_workflow_xyz"])
        assert result.returncode == 1
        assert "Unknown workflow" in result.stdout


class TestCLIInit:
    """Test init command."""

    def test_init_no_args(self):
        """Test init with no arguments."""
        result = run_cli(["init"])
        assert result.returncode == 1
        assert "Usage:" in result.stdout


class TestCLIBuild:
    """Test build command."""

    def test_build_no_blueprint(self):
        """Test build in directory without blueprint."""
        result = run_cli(["build", "/tmp"])
        assert result.returncode == 1
        assert "No blueprint found" in result.stdout


class TestCLITLA:
    """Test tla command."""

    def test_tla_no_args(self):
        """Test tla with no arguments."""
        result = run_cli(["tla"])
        assert result.returncode == 1
        assert "Usage:" in result.stdout


class TestUtilityRunFunction:
    """Test utilities via Python run() function directly."""

    def test_logic_decoder_run(self):
        """Test logic_decoder run function."""
        from lpp.util.logic_decoder import run
        result = run({"file_path": str(SAMPLE_PYTHON)})
        assert result.get("state") == "complete"
        assert result.get("error") is None

    def test_blueprint_linter_run(self):
        """Test blueprint_linter run function."""
        from lpp.util.blueprint_linter import run
        result = run({"blueprint_path": str(SAMPLE_BLUEPRINT)})
        assert result.get("state") == "complete"
        assert result.get("error") is None

    def test_test_generator_run(self):
        """Test test_generator run function."""
        from lpp.util.test_generator import run
        result = run({"blueprint_path": str(SAMPLE_BLUEPRINT)})
        assert result.get("state") == "complete"
        assert result.get("error") is None

    def test_skill_contractor_run(self):
        """Test skill_contractor run function."""
        from lpp.util.skill_contractor import run
        result = run({})
        assert result.get("state") == "idle"
        assert result.get("error") is None

    def test_doc_generator_run(self):
        """Test doc_generator run function."""
        from lpp.util.doc_generator import run
        result = run({"utilsPath": str(UTILS_DIR), "options": {"all": True}})
        assert result.get("state") == "complete"
        assert result.get("error") is None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
