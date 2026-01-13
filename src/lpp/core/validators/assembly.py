"""
L++ Assembly Validator

Validates assembly blueprints that compose pre-verified component blueprints.
Components are treated as atomic actions with defined terminal outcomes.

Key principle: Assembly verification reasons about component terminals and
contracts, not internal states. This enables hierarchical verification
without combinatorial explosion.

Verification Levels:
    1. Static: Schema validation, interface compatibility
    2. Dynamic: Cross-component invariants via TLA+ generation
"""

import json
import os
from typing import Any, Dict, List, Optional, Tuple


class AssemblyValidationError(Exception):
    """Error during assembly validation."""
    pass


class ComponentLoadError(AssemblyValidationError):
    """Error loading a component blueprint."""
    pass


class InterfaceCompatibilityError(AssemblyValidationError):
    """Interface mismatch between components."""
    pass


class MissingTerminalError(AssemblyValidationError):
    """Required terminal not defined in component."""
    pass


def _getTerminalIds(bp: Dict) -> set:
    """Get terminal state IDs from blueprint (handles v0.2.0 and legacy)."""
    termStates = bp.get('terminal_states', {})
    if isinstance(termStates, dict):
        return set(termStates.keys())
    return set(termStates)


def loadAssembly(assemblyPath: str) -> Tuple[Dict, Dict[str, Dict]]:
    """
    Load an assembly blueprint and all its component blueprints.

    Args:
        assemblyPath: Path to assembly JSON file

    Returns:
        Tuple of (assembly_dict, components_dict)
        where components_dict maps alias to loaded component blueprint

    Raises:
        AssemblyValidationError: If assembly or components cannot be loaded
    """
    # Load assembly
    try:
        with open(assemblyPath, 'r') as f:
            assembly = json.load(f)
    except FileNotFoundError:
        raise AssemblyValidationError(f"Assembly not found: {assemblyPath}")
    except json.JSONDecodeError as e:
        raise AssemblyValidationError(f"Invalid JSON in assembly: {e}")

    # Validate schema
    schema = assembly.get('$schema', '')
    if not schema.startswith('lpp/assembly'):
        raise AssemblyValidationError(
            f"Invalid schema: {schema}, expected lpp/assembly/*")

    # Load components
    assemblyDir = os.path.dirname(os.path.abspath(assemblyPath))
    components = {}

    for alias, compDef in assembly.get('components', {}).items():
        bpPath = compDef.get('blueprint')
        if not bpPath:
            raise ComponentLoadError(f"No blueprint path for component: {alias}")

        # Resolve relative paths from assembly location
        if not os.path.isabs(bpPath):
            bpPath = os.path.join(assemblyDir, bpPath)

        try:
            with open(bpPath, 'r') as f:
                components[alias] = json.load(f)
        except FileNotFoundError:
            raise ComponentLoadError(
                f"Component blueprint not found: {bpPath} (alias: {alias})")
        except json.JSONDecodeError as e:
            raise ComponentLoadError(
                f"Invalid JSON in component {alias}: {e}")

    return assembly, components


def validateTerminals(
    assembly: Dict,
    components: Dict[str, Dict]
) -> List[str]:
    """
    Validate that required terminals exist in components.

    Args:
        assembly: Assembly blueprint dict
        components: Dict mapping alias to component blueprint

    Returns:
        List of validation errors (empty if valid)
    """
    errors = []

    for alias, compDef in assembly.get('components', {}).items():
        reqTerminals = compDef.get('required_terminals', [])
        component = components.get(alias, {})
        compTerminals = _getTerminalIds(component)

        for term in reqTerminals:
            if term not in compTerminals:
                errors.append(
                    f"Component '{alias}' missing required terminal: {term}. "
                    f"Available: {list(compTerminals)}")

    return errors


def validateInterfaces(
    assembly: Dict,
    components: Dict[str, Dict]
) -> List[str]:
    """
    Validate interface compatibility between components.

    Checks that when assembly wires component A's output to component B's input,
    the types are compatible.

    Args:
        assembly: Assembly blueprint dict
        components: Dict mapping alias to component blueprint

    Returns:
        List of validation errors (empty if valid)
    """
    errors = []

    # Build output schemas from terminal contracts
    outputSchemas = {}
    for alias, comp in components.items():
        contracts = comp.get('terminal_contracts', {})
        outputSchemas[alias] = {}
        for terminal, contract in contracts.items():
            outSchema = contract.get('output_schema', {})
            for field, schema in outSchema.items():
                outputSchemas[alias][f"{terminal}.{field}"] = schema
                # Also add without terminal prefix for convenience
                outputSchemas[alias][field] = schema

    # Build input schemas from component context_schema
    inputSchemas = {}
    for alias, comp in components.items():
        ctx = comp.get('context_schema', {}).get('properties', {})
        inputSchemas[alias] = ctx

    # Check input_map compatibility in component definitions
    for alias, compDef in assembly.get('components', {}).items():
        inputMap = compDef.get('input_map', {})

        for targetField, sourcePath in inputMap.items():
            # Parse source path: "other_component.output.field" or
            # "assembly.context.field"
            parts = sourcePath.split('.')

            if len(parts) < 2:
                errors.append(
                    f"Invalid input_map path: {sourcePath} for {alias}")
                continue

            sourceAlias = parts[0]

            if sourceAlias == 'assembly':
                # Source is assembly context - skip type checking for now
                continue

            # Source is another component's output
            if sourceAlias not in outputSchemas:
                errors.append(
                    f"Unknown source component: {sourceAlias} in {alias}.input_map")
                continue

            # Get the field (last part of path)
            sourceField = parts[-1]
            sourceSchema = outputSchemas[sourceAlias].get(sourceField)
            targetSchema = inputSchemas.get(alias, {}).get(targetField)

            if sourceSchema and targetSchema:
                srcType = sourceSchema.get('type')
                tgtType = targetSchema.get('type')
                if srcType and tgtType and srcType != tgtType:
                    errors.append(
                        f"Type mismatch: {sourceAlias}.{sourceField} ({srcType}) -> "
                        f"{alias}.{targetField} ({tgtType})")

    return errors


def validateInvariants(assembly: Dict) -> List[str]:
    """
    Validate assembly invariant definitions are well-formed.

    Args:
        assembly: Assembly blueprint dict

    Returns:
        List of validation errors (empty if valid)
    """
    errors = []
    invariants = assembly.get('assembly_invariants', [])

    for inv in invariants:
        invId = inv.get('id', '<no id>')

        if 'type' not in inv:
            errors.append(f"Invariant {invId} missing 'type' field")
            continue

        invType = inv['type']

        if invType == 'state_dependency':
            if 'expression' not in inv:
                errors.append(
                    f"Invariant {invId}: state_dependency requires 'expression'")

        elif invType == 'contract_match':
            check = inv.get('check', {})
            if not check.get('source') or not check.get('target'):
                errors.append(
                    f"Invariant {invId}: contract_match requires 'check.source' "
                    "and 'check.target'")

        elif invType == 'sequence':
            if 'expression' not in inv:
                errors.append(
                    f"Invariant {invId}: sequence requires 'expression'")

    return errors


def validateAssembly(assemblyPath: str) -> Tuple[bool, List[str]]:
    """
    Perform full static validation of an assembly blueprint.

    Args:
        assemblyPath: Path to assembly JSON file

    Returns:
        Tuple of (is_valid, list_of_errors)
    """
    allErrors = []

    try:
        assembly, components = loadAssembly(assemblyPath)
    except AssemblyValidationError as e:
        return False, [str(e)]

    # Validate terminals
    terminalErrors = validateTerminals(assembly, components)
    allErrors.extend(terminalErrors)

    # Validate interfaces
    interfaceErrors = validateInterfaces(assembly, components)
    allErrors.extend(interfaceErrors)

    # Validate invariant definitions
    invariantErrors = validateInvariants(assembly)
    allErrors.extend(invariantErrors)

    return len(allErrors) == 0, allErrors


def generateAssemblyTla(
    assembly: Dict,
    components: Dict[str, Dict],
    outputDir: str = None
) -> str:
    """
    Generate TLA+ specification for assembly-level verification.

    Components are treated as atomic actions with non-deterministic
    terminal outcomes. This avoids combinatorial explosion.

    Args:
        assembly: Assembly blueprint dict
        components: Dict mapping alias to component blueprint
        outputDir: Optional directory to write TLA+ files

    Returns:
        Generated TLA+ specification as string
    """
    assemblyId = assembly.get('id', 'Assembly')
    moduleName = _tlaIdent(assemblyId)

    lines = []
    lines.append(f"--------------------------- MODULE {moduleName} ---------------------------")
    lines.append("")
    lines.append("EXTENDS Integers, Sequences, TLC")
    lines.append("")

    # Variables
    lines.append("VARIABLES")
    lines.append("    meta_state,           \\* Current assembly state")

    # Add context variables
    ctxProps = assembly.get('context_schema', {}).get('properties', {})
    for prop in ctxProps.keys():
        lines.append(f"    ctx_{_tlaIdent(prop)},")

    # Add component terminal tracking
    for alias in components.keys():
        lines.append(f"    {_tlaIdent(alias)}_terminal,")

    # Remove trailing comma from last variable
    if lines[-1].endswith(','):
        lines[-1] = lines[-1][:-1]

    lines.append("")

    # Define terminal sets for each component
    lines.append("(* Component terminal sets *)")
    for alias, comp in components.items():
        terminals = list(_getTerminalIds(comp))
        termSet = ", ".join(f'"{t}"' for t in terminals)
        lines.append(f"{_tlaIdent(alias)}Terminals == {{{termSet}, \"PENDING\"}}")
    lines.append("")

    # Assembly states
    assemblyStates = list(assembly.get('states', {}).keys())
    stateSet = ", ".join(f'"{s}"' for s in assemblyStates)
    lines.append(f"AssemblyStates == {{{stateSet}}}")
    lines.append("")

    # NULL constant
    lines.append("NULL == \"__NULL__\"")
    lines.append("")

    # Type invariant
    lines.append("TypeInvariant ==")
    lines.append("    /\\ meta_state \\in AssemblyStates")
    for alias in components.keys():
        lines.append(f"    /\\ {_tlaIdent(alias)}_terminal \\in {_tlaIdent(alias)}Terminals")
    lines.append("")

    # Init
    entryState = assembly.get('entry_state', 'idle')
    lines.append("Init ==")
    lines.append(f'    /\\ meta_state = "{entryState}"')
    for prop in ctxProps.keys():
        lines.append(f"    /\\ ctx_{_tlaIdent(prop)} = NULL")
    for alias in components.keys():
        lines.append(f'    /\\ {_tlaIdent(alias)}_terminal = "PENDING"')
    lines.append("")

    # Generate actions for each transition
    transitions = assembly.get('transitions', [])
    actionNames = []

    for trans in transitions:
        transId = trans.get('id', 'unknown')
        actionName = _tlaIdent(transId)
        actionNames.append(actionName)

        fromState = trans.get('from')
        toState = trans.get('to')
        onEvent = trans.get('on_event', '')

        lines.append(f"(* Transition: {transId} *)")
        lines.append(f"{actionName} ==")
        lines.append(f'    /\\ meta_state = "{fromState}"')

        # Handle component terminal events
        if ':TERMINAL' in onEvent:
            compAlias = onEvent.split(':')[0]
            # Component must have reached a terminal
            lines.append(f'    /\\ {_tlaIdent(compAlias)}_terminal /= "PENDING"')

            # Add gate conditions if present
            gates = trans.get('gates', [])
            for gateId in gates:
                gate = assembly.get('gates', {}).get(gateId, {})
                expr = gate.get('expression', 'TRUE')
                tlaExpr = _exprToTla(expr, components)
                lines.append(f"    /\\ {tlaExpr}")

        lines.append(f'    /\\ meta_state\' = "{toState}"')

        # Check if entering a component execution state
        toStateDef = assembly.get('states', {}).get(toState, {})
        if toStateDef.get('type') == 'component_execution':
            execComp = toStateDef.get('component')
            if execComp:
                # Non-deterministically choose a terminal for this component
                compTerminals = list(_getTerminalIds(components.get(execComp, {})))
                if compTerminals:
                    termSet = ", ".join(f'"{t}"' for t in compTerminals)
                    lines.append(f"    /\\ {_tlaIdent(execComp)}_terminal' \\in {{{termSet}}}")

        # UNCHANGED for other variables
        unchanged = []
        for prop in ctxProps.keys():
            unchanged.append(f"ctx_{_tlaIdent(prop)}")
        for alias in components.keys():
            if not (toStateDef.get('type') == 'component_execution' and
                    toStateDef.get('component') == alias):
                unchanged.append(f"{_tlaIdent(alias)}_terminal")

        if unchanged:
            lines.append(f"    /\\ UNCHANGED <<{', '.join(unchanged)}>>")

        lines.append("")

    # Next relation
    if actionNames:
        lines.append("Next ==")
        lines.append("    \\/ " + "\n    \\/ ".join(actionNames))
    else:
        lines.append("Next == FALSE")
    lines.append("")

    # Spec
    lines.append("Spec == Init /\\ [][Next]_<<meta_state, " +
                 ", ".join(f"ctx_{_tlaIdent(p)}" for p in ctxProps.keys()) +
                 (", " if ctxProps else "") +
                 ", ".join(f"{_tlaIdent(a)}_terminal" for a in components.keys()) +
                 ">>")
    lines.append("")

    # Assembly invariants
    invariants = assembly.get('assembly_invariants', [])
    for inv in invariants:
        invId = inv.get('id', 'Unknown')
        invType = inv.get('type')

        if invType == 'state_dependency':
            expr = inv.get('expression', 'TRUE')
            tlaExpr = _exprToTla(expr, components)
            lines.append(f"(* {inv.get('name', invId)} *)")
            lines.append(f"{_tlaIdent(invId)} == {tlaExpr}")
            lines.append("")

        elif invType == 'sequence':
            expr = inv.get('expression', 'TRUE')
            tlaExpr = _exprToTla(expr, components)
            lines.append(f"(* {inv.get('name', invId)} *)")
            lines.append(f"{_tlaIdent(invId)} == {tlaExpr}")
            lines.append("")

    lines.append("=============================================================================")

    tlaSpec = "\n".join(lines)

    # Write to file if output dir specified
    if outputDir:
        os.makedirs(outputDir, exist_ok=True)
        tlaPath = os.path.join(outputDir, f"{moduleName}.tla")
        with open(tlaPath, 'w') as f:
            f.write(tlaSpec)

        # Generate config file
        cfgLines = []
        cfgLines.append("SPECIFICATION Spec")
        cfgLines.append("")
        cfgLines.append("INVARIANT TypeInvariant")
        for inv in invariants:
            invId = inv.get('id')
            if invId:
                cfgLines.append(f"INVARIANT {_tlaIdent(invId)}")
        cfgLines.append("")
        cfgLines.append("CHECK_DEADLOCK FALSE")

        cfgPath = os.path.join(outputDir, f"{moduleName}.cfg")
        with open(cfgPath, 'w') as f:
            f.write("\n".join(cfgLines))

    return tlaSpec


def _tlaIdent(s: str) -> str:
    """Convert string to valid TLA+ identifier."""
    result = s.replace('-', '_').replace('.', '_').replace(' ', '_')
    # Ensure starts with letter
    if result and not result[0].isalpha():
        result = 'x_' + result
    return result


def _exprToTla(expr: str, components: Dict[str, Dict]) -> str:
    """
    Convert L++ expression to TLA+ expression.

    Handles:
    - component._terminal references
    - context variable references
    - comparison operators
    """
    # Replace Python operators with TLA+
    tla = expr
    tla = tla.replace(' == ', ' = ')
    tla = tla.replace(' != ', ' /= ')
    tla = tla.replace(' and ', ' /\\ ')
    tla = tla.replace(' or ', ' \\/ ')
    tla = tla.replace(' not ', ' ~ ')
    tla = tla.replace(' None', ' NULL')
    tla = tla.replace('None ', 'NULL ')
    tla = tla.replace(' => ', ' => ')

    # Replace _state with meta_state
    tla = tla.replace('_state', 'meta_state')

    # Replace component terminal references
    for alias in components.keys():
        tla = tla.replace(f'{alias}._terminal', f'{_tlaIdent(alias)}_terminal')

    # Replace context references
    tla = tla.replace('ctx.', 'ctx_')

    return tla


# =============================================================================
# CLI
# =============================================================================

def main():
    """Command-line interface for assembly validation."""
    import sys

    if len(sys.argv) < 2:
        print("Usage: python -m frame_py.assembly_validator <assembly.json> [--tla <output_dir>]")
        print("")
        print("Options:")
        print("  --tla <dir>  Generate TLA+ specification to directory")
        sys.exit(1)

    assemblyPath = sys.argv[1]
    tlaDir = None

    if '--tla' in sys.argv:
        tlaIdx = sys.argv.index('--tla')
        if tlaIdx + 1 < len(sys.argv):
            tlaDir = sys.argv[tlaIdx + 1]

    print(f"[L++ Assembly Validator] Loading: {assemblyPath}")
    print("")

    isValid, errors = validateAssembly(assemblyPath)

    if errors:
        print("Validation Errors:")
        for err in errors:
            print(f"  - {err}")
        print("")

    if isValid:
        print("[PASS] Assembly validation passed")

        if tlaDir:
            print(f"\nGenerating TLA+ to: {tlaDir}")
            assembly, components = loadAssembly(assemblyPath)
            tlaSpec = generateAssemblyTla(assembly, components, tlaDir)
            print(f"Generated: {assembly.get('id', 'Assembly')}.tla")
    else:
        print("[FAIL] Assembly validation failed")
        sys.exit(1)


if __name__ == '__main__':
    main()
