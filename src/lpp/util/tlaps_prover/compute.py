"""
TLAPS Prover Compute Functions

Wraps the TLAPS proof generator functionality.
"""
import json
import sys
from pathlib import Path


def generate(params: dict) -> dict:
    """Generate TLAPS-ready TLA+ spec from blueprint."""
    bp_path = params.get("blueprintPath")
    output_dir = params.get("outputDir", ".")

    if not bp_path:
        return {"error": "blueprintPath required"}

    bp_file = Path(bp_path)
    if not bp_file.exists():
        return {"error": f"Blueprint not found: {bp_path}"}

    # Import the generator from utils
    utils_path = Path(__file__).parent.parent.parent.parent.parent
    gen_path = utils_path / "utils" / "tlaps_prover"
    sys.path.insert(0, str(gen_path))

    try:
        from tlaps_proof_generator import loadBlueprint, generateTlapsSpec

        bp = loadBlueprint(str(bp_file))
        module_name = bp.get("id", bp_file.stem)
        tla_spec = generateTlapsSpec(bp, module_name)

        # Write output
        out_dir = Path(output_dir)
        out_dir.mkdir(parents=True, exist_ok=True)
        out_file = out_dir / f"{module_name}_proof.tla"
        out_file.write_text(tla_spec)

        return {"tlaSpec": str(out_file)}
    except ImportError:
        return {"error": "TLAPS generator not found"}
    except Exception as e:
        return {"error": str(e)}


def verify(params: dict) -> dict:
    """Run TLAPS verification on generated spec."""
    import subprocess

    tla_spec = params.get("tlaSpec")
    if not tla_spec:
        return {"error": "tlaSpec required"}

    spec_file = Path(tla_spec)
    if not spec_file.exists():
        return {"error": f"TLA+ spec not found: {tla_spec}"}

    try:
        result = subprocess.run(
            ["tlapm", str(spec_file)],
            capture_output=True,
            text=True,
            timeout=300
        )
        return {
            "proofResult": {
                "success": result.returncode == 0,
                "stdout": result.stdout,
                "stderr": result.stderr
            }
        }
    except FileNotFoundError:
        return {"proofResult": {"success": False, "error": "tlapm not found"}}
    except subprocess.TimeoutExpired:
        return {"proofResult": {"success": False, "error": "Timeout"}}
    except Exception as e:
        return {"proofResult": {"success": False, "error": str(e)}}


COMPUTE_REGISTRY = {
    ("tlaps", "generate"): generate,
    ("tlaps", "verify"): verify,
}
