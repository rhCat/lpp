#!/usr/bin/env python3
"""
L++ Skill Contractor - Minimal Extrusion Layer
Per build_rules.md: thin dispatch wrapper with auto-loop support.

v1.7.0: Autonomous L++ skill generator with code sanitization.
- Each run creates runs/<timestamp>/ with state.json and step logs.
- stdout/stderr captured to runs/<timestamp>/stdout.log
"""
from frame_py.compiler import compile_blueprint
from src.skill_contractor_compute import COMPUTE_UNITS, save_state, load_state
import sys
import time
import io
from pathlib import Path
from datetime import datetime

sys.path.insert(0, str(Path(__file__).parent.parent / "src"))


HERE = Path(__file__).parent
RUNS_DIR = HERE / "runs"


class TeeLogger:
    """Tee stdout/stderr to file while preserving console output."""

    def __init__(self, logPath: Path):
        self.logPath = logPath
        self.logFile = open(logPath, "a", buffering=1)  # Line buffered
        self.stdout = sys.stdout
        self.stderr = sys.stderr

    def write(self, data):
        self.stdout.write(data)
        self.stdout.flush()
        try:
            self.logFile.write(data)
            self.logFile.flush()
        except:
            pass

    def flush(self):
        self.stdout.flush()
        try:
            self.logFile.flush()
        except:
            pass

    def __enter__(self):
        sys.stdout = self
        sys.stderr = self
        return self

    def __exit__(self, *args):
        sys.stdout = self.stdout
        sys.stderr = self.stderr
        self.logFile.close()


def compileAndLoad(blueprintJson: str, registry: dict):
    """Compile blueprint and return operator with COMPUTE registry."""
    import importlib.util
    out = HERE / "results" / f"{Path(blueprintJson).stem}_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(blueprintJson, str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    reg = {tuple(k.split(":")): fn for k, fn in registry.items()}
    return mod.create_operator(reg)


def listRuns():
    """List existing runs."""
    if not RUNS_DIR.exists():
        print("No runs found.")
        return []
    runs = sorted(RUNS_DIR.iterdir(), reverse=True)
    if not runs:
        print("No runs found.")
        return []

    print("\nExisting runs:")
    validRuns = []
    for i, run in enumerate(runs[:10]):  # Show last 10
        stateFile = run / "state.json"
        if stateFile.exists():
            import json
            state = json.loads(stateFile.read_text())
            target = (state.get("target") or "")[:40]
            fsmState = state.get("fsm_state", "?")
            score = state.get("score", "?")
            validRuns.append(run)
            print(f"  [{i}] {run.name}: {fsmState} | score={score} | {target}...")
    return validRuns


def _safeStr(val, default="Unknown", maxLen=100):
    """Safely convert value to string with truncation."""
    if val is None:
        return default
    s = str(val)
    if len(s) > maxLen:
        return s[:maxLen] + "..."
    return s


def runLoop(op, autoMode=False, tee=None):
    """Run the agent loop until complete or error."""
    runDir = op.context.get("run_dir", str(HERE))

    while op.state not in ("complete",):
        ctx = op.context
        failedSteps = ctx.get("failed_steps") or []
        maxErr = ctx.get("max_errors") or 3
        stepErr = ctx.get("step_error_count") or 0
        repairAttempts = ctx.get("repair_attempts") or 0
        error = ctx.get("error")
        parseError = ctx.get("parse_error")

        if op.state == "error":
            errMsg = _safeStr(error, "Unknown error")
            print(f"  [ERROR] Step error ({stepErr}/{maxErr}): {errMsg}")
            if stepErr < maxErr:
                print("  [RETRYING] Same step...")
            else:
                print("  [REVIEWING] Step failed too many times, deciding...")
        elif op.state == "reviewing":
            decision = ctx.get('review_decision', 'pending')
            print(f"  [REVIEWING] Decision: {decision} | "
                  f"Failed steps: {len(failedSteps)}")
        elif op.state == "parsing":
            maxRepairs = ctx.get('max_repairs') or 3
            print(f"  [PARSING] Repair attempt {repairAttempts}/{maxRepairs}")
            if parseError:
                print(f"    Error: {_safeStr(parseError, maxLen=150)}")
        else:
            stepIdx = ctx.get('step_index') or 0
            stepCnt = ctx.get('step_count') or 0
            iterN = ctx.get('iteration') or 0
            currentStep = ctx.get('current_step') or {}
            action = _safeStr(currentStep.get('action'), 'N/A', 50)
            print(f"  [{op.state}] Step {stepIdx+1}/{stepCnt} | "
                  f"Iter {iterN} | Failed {len(failedSteps)} | {action}")

        op.dispatch("DONE", {})
        save_state({"run_dir": runDir, "fsm_state": op.state, **op.context})

        if autoMode:
            time.sleep(0.5)

    return op.context


def resumeRun(runDir: Path, op):
    """Resume from an existing run folder."""
    saved = load_state({"run_dir": str(runDir)})
    if not saved.get("has_saved_state"):
        print(f"No state found in {runDir}")
        return False

    print(f"\nResuming run: {runDir.name}")
    print(f"  Target: {_safeStr(saved.get('target'), 'N/A', 60)}")
    print(f"  State: {saved.get('fsm_state')} | Score: {saved.get('score')}")

    # Restore context
    for k, v in saved.items():
        if k not in ("has_saved_state",) and v is not None:
            op.context[k] = v

    # Restore FSM state
    fsmState = saved.get("fsm_state")
    if fsmState and fsmState != "idle":
        op._state = fsmState

    return True


def main():
    """CLI for skill contractor with continuous mode."""
    op = compileAndLoad(str(HERE / "skill_contractor.json"), COMPUTE_UNITS)
    op.dispatch("START", {})

    print("Skill Contractor v1.7.0")
    print("Commands: quit, status, auto, reset, runs, resume <n>, logs")
    print("Or enter a coding target to begin.\n")

    tee = None  # Will be set when a run starts

    while True:
        try:
            cmd = input(f"[{op.state}] > ").strip()
            if not cmd:
                continue

            if cmd.lower() in ("quit", "exit", "q"):
                break

            if cmd.lower() == "status":
                ctx = op.context
                stepIdx = ctx.get('step_index') or 0
                stepCnt = ctx.get('step_count') or 0
                print(f"  State: {op.state} | Step {stepIdx+1}/{stepCnt}")
                print(
                    f"  Iter: {ctx.get('iteration')} | Score: {ctx.get('score')}")
                print(f"  Target: {_safeStr(ctx.get('target'), 'None', 60)}")
                print(f"  Run: {ctx.get('run_id', 'N/A')}")
                if ctx.get("feedback"):
                    print(
                        f"  Feedback: {_safeStr(ctx['feedback'], maxLen=100)}")
                if ctx.get("error"):
                    print(f"  Error: {_safeStr(ctx['error'], maxLen=100)}")
                continue

            if cmd.lower() == "reset":
                op = compileAndLoad(
                    str(HERE / "skill_contractor.json"), COMPUTE_UNITS)
                op.dispatch("START", {})
                print("Reset to idle with new run.")
                continue

            if cmd.lower() == "runs":
                listRuns()
                continue

            if cmd.lower().startswith("resume"):
                parts = cmd.split()
                if len(parts) < 2:
                    validRuns = listRuns()
                    if validRuns:
                        print("Usage: resume <n> to resume run number")
                    continue

                try:
                    idx = int(parts[1])
                    validRuns = sorted(RUNS_DIR.iterdir(), reverse=True)[:10]
                    if 0 <= idx < len(validRuns):
                        runDir = validRuns[idx]
                        if resumeRun(runDir, op):
                            # Start logging to stdout.log
                            stdoutLog = runDir / "stdout.log"
                            with TeeLogger(stdoutLog) as tee:
                                print(
                                    f"\n=== Resuming {runDir.name} at {datetime.now()} ===")
                                if op.state not in ("complete", "idle"):
                                    runLoop(op, autoMode=True, tee=tee)
                                    print(
                                        f"\nFinal: {op.state} | Score: {op.context.get('score')}")
                    else:
                        print(f"Invalid run index: {idx}")
                except ValueError:
                    print("Usage: resume <n> where n is run index")
                continue

            if cmd.lower() == "auto":
                if op.state not in ("complete", "idle"):
                    runDir = op.context.get("run_dir")
                    if runDir:
                        stdoutLog = Path(runDir) / "stdout.log"
                        with TeeLogger(stdoutLog) as tee:
                            runLoop(op, autoMode=True, tee=tee)
                    else:
                        runLoop(op, autoMode=True)
                    print(
                        f"\nFinal: {op.state} | Score: {op.context.get('score')}")
                else:
                    print("Nothing to run. Submit a target first.")
                continue

            if cmd.lower() == "logs":
                runDir = op.context.get("run_dir")
                if runDir:
                    runPath = Path(runDir)
                    # Show stdout.log
                    stdoutLog = runPath / "stdout.log"
                    if stdoutLog.exists():
                        print(f"\n=== Stdout Log ({runPath.name}) ===")
                        print(stdoutLog.read_text()[-3000:])
                    # Show run.log
                    logFile = runPath / "run.log"
                    if logFile.exists():
                        print(f"\n=== Run Log ({runPath.name}) ===")
                        print(logFile.read_text()[-2000:])
                    # Show current step log
                    stepIdx = op.context.get("step_index", 0)
                    stepLog = runPath / f"step_{stepIdx}.log"
                    if stepLog.exists():
                        print(f"\n=== Step {stepIdx} Log ===")
                        print(stepLog.read_text()[-2000:])
                else:
                    print("No active run.")
                continue

            # Submit new target - start logging immediately
            op.dispatch("SUBMIT", {"target": cmd})
            runDir = op.context.get("run_dir")
            runId = op.context.get("run_id", "?")
            print(f"Target submitted. Run: {runId}")

            if runDir:
                stdoutLog = Path(runDir) / "stdout.log"
                with TeeLogger(stdoutLog) as tee:
                    print(f"\n=== Run {runId} started at {datetime.now()} ===")
                    print(f"Target: {cmd}")
                    runLoop(op, autoMode=True, tee=tee)
                    print(
                        f"\nFinal: {op.state} | Score: {op.context.get('score')}")
            else:
                runLoop(op, autoMode=True)
                print(
                    f"\nFinal: {op.state} | Score: {op.context.get('score')}")

            print(f"Logs: {runDir or HERE}")

        except (KeyboardInterrupt, EOFError):
            runDir = op.context.get("run_dir")
            if runDir:
                save_state(
                    {"run_dir": runDir, "fsm_state": op.state, **op.context})
                print(f"\nInterrupted. State saved to {runDir}")
            else:
                print("\nInterrupted.")
            break

    print("Done.")


if __name__ == "__main__":
    main()
