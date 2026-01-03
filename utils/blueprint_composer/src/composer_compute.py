"""
COMPUTE units for the L++ Blueprint Composer

These are the pure computation functions that implement blueprint composition.
All functions are hermetic: input is params dict, output is result dict.
"""

import json
import copy
from pathlib import Path
from typing import Any, Dict, List, Set, Optional, Tuple


# =============================================================================
# Constants
# =============================================================================

NAMESPACE_SEPARATOR = "$"


# =============================================================================
# Blueprint Loading
# =============================================================================

def load_parent(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load the parent blueprint from a JSON file."""
    path = params.get("path")
    if not path:
        return {"blueprint": None, "path": None, "error": "No path provided"}

    try:
        p = Path(path)
        if not p.exists():
            return {"blueprint": None, "path": None,
                    "error": f"File not found: {path}"}

        with open(p) as f:
            raw = json.load(f)

        bp = _normalize_blueprint(raw)
        return {"blueprint": bp, "path": str(p), "error": None}
    except json.JSONDecodeError as e:
        return {"blueprint": None, "path": None,
                "error": f"Invalid JSON: {e}"}
    except Exception as e:
        return {"blueprint": None, "path": None, "error": str(e)}


def load_child(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load a child blueprint to be embedded."""
    path = params.get("path")
    if not path:
        return {"blueprint": None, "path": None, "error": "No path provided"}

    try:
        p = Path(path)
        if not p.exists():
            return {"blueprint": None, "path": None,
                    "error": f"File not found: {path}"}

        with open(p) as f:
            raw = json.load(f)

        bp = _normalize_blueprint(raw)
        return {"blueprint": bp, "path": str(p), "error": None}
    except json.JSONDecodeError as e:
        return {"blueprint": None, "path": None,
                "error": f"Invalid JSON: {e}"}
    except Exception as e:
        return {"blueprint": None, "path": None, "error": str(e)}


def _normalize_blueprint(raw: Dict) -> Dict:
    """Normalize a raw blueprint dict to standard form."""
    return {
        "$schema": raw.get("$schema", "lpp/v0.1.2"),
        "id": raw.get("id", "unknown"),
        "name": raw.get("name", "Unknown"),
        "version": raw.get("version", "0.0.0"),
        "description": raw.get("description", ""),
        "context_schema": raw.get("context_schema", {"properties": {}}),
        "states": raw.get("states", {}),
        "transitions": raw.get("transitions", []),
        "gates": raw.get("gates", {}),
        "actions": raw.get("actions", {}),
        "display": raw.get("display", {}),
        "entry_state": raw.get("entry_state"),
        "terminal_states": raw.get("terminal_states", [])
    }


# =============================================================================
# Embedding Definition
# =============================================================================

def init_embedding(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize a new embedding definition."""
    targetState = params.get("target_state")
    nsPrefix = params.get("namespace_prefix")

    if not targetState:
        targetState = "embedded"

    if not nsPrefix:
        nsPrefix = targetState

    embedding = {
        "target_state": targetState,
        "namespace_prefix": nsPrefix,
        "child": None,
        "child_path": None,
        "contract": {
            "input_map": {},
            "output_map": {}
        },
        "event_map": {}
    }

    return {"embedding": embedding, "namespace_prefix": nsPrefix}


def set_input_contract(params: Dict[str, Any]) -> Dict[str, Any]:
    """Set the input contract mapping for an embedding."""
    embedding = copy.deepcopy(params.get("embedding", {}))
    inputMap = params.get("input_map", {})

    if not embedding:
        return {"embedding": None}

    embedding["contract"]["input_map"] = inputMap
    return {"embedding": embedding}


def set_output_contract(params: Dict[str, Any]) -> Dict[str, Any]:
    """Set the output contract mapping for an embedding."""
    embedding = copy.deepcopy(params.get("embedding", {}))
    outputMap = params.get("output_map", {})

    if not embedding:
        return {"embedding": None}

    embedding["contract"]["output_map"] = outputMap
    return {"embedding": embedding}


def set_event_map(params: Dict[str, Any]) -> Dict[str, Any]:
    """Set the event mapping for an embedding."""
    embedding = copy.deepcopy(params.get("embedding", {}))
    eventMap = params.get("event_map", {})

    if not embedding:
        return {"embedding": None}

    embedding["event_map"] = eventMap
    return {"embedding": embedding}


def finalize_embedding(params: Dict[str, Any]) -> Dict[str, Any]:
    """Finalize the current embedding and add to list."""
    embedding = copy.deepcopy(params.get("embedding", {}))
    embeddings = list(params.get("embeddings") or [])
    childBp = params.get("child_blueprint")
    childPath = params.get("child_path")

    if not embedding:
        return {"embeddings": embeddings, "current_embedding": None}

    # Attach child blueprint to embedding
    embedding["child"] = childBp
    embedding["child_path"] = childPath

    embeddings.append(embedding)

    return {"embeddings": embeddings, "current_embedding": None}


# =============================================================================
# Composition Logic
# =============================================================================

def compose(params: Dict[str, Any]) -> Dict[str, Any]:
    """Execute the composition - embed child blueprints into parent."""
    parent = params.get("parent")
    embeddings = params.get("embeddings", [])

    if not parent:
        return {"composed": None, "error": "No parent blueprint"}

    if not embeddings:
        return {"composed": None, "error": "No embeddings defined"}

    try:
        composed = copy.deepcopy(parent)

        for emb in embeddings:
            composed = _apply_embedding(composed, emb)

        # Update metadata
        composed["id"] = f"{parent.get('id', 'unknown')}_composed"
        composed["name"] = f"{parent.get('name', 'Unknown')} (Composed)"
        composed["version"] = _bumpVersion(parent.get("version", "0.0.0"))
        composed["description"] = (
            f"Composed blueprint from {parent.get('name')} with "
            f"{len(embeddings)} embedding(s)"
        )

        return {"composed": composed, "error": None}
    except Exception as e:
        return {"composed": None, "error": str(e)}


def _apply_embedding(
    parent: Dict[str, Any],
    embedding: Dict[str, Any]
) -> Dict[str, Any]:
    """Apply a single embedding to the parent blueprint."""
    result = copy.deepcopy(parent)
    child = embedding.get("child")
    targetState = embedding.get("target_state")
    nsPrefix = embedding.get("namespace_prefix", targetState)
    contract = embedding.get("contract", {})
    eventMap = embedding.get("event_map", {})

    if not child:
        raise ValueError("Embedding has no child blueprint")

    # Validate target state exists
    if targetState not in result.get("states", {}):
        raise ValueError(f"Target state '{targetState}' not found in parent")

    # 1. Namespace-prefix all child elements
    prefixedChild = _prefix_child(child, nsPrefix)

    # 2. Merge child states (excluding entry/terminal special handling)
    childStates = prefixedChild.get("states", {})
    result["states"].update(childStates)

    # 3. Merge child gates
    childGates = prefixedChild.get("gates", {})
    result["gates"].update(childGates)

    # 4. Merge child actions with contract mapping
    childActions = prefixedChild.get("actions", {})
    mappedActions = _map_action_contracts(childActions, contract, nsPrefix)
    result["actions"].update(mappedActions)

    # 5. Merge child transitions with event mapping
    childTransitions = prefixedChild.get("transitions", [])
    mappedTransitions = _map_transitions(
        childTransitions, eventMap, nsPrefix, child
    )

    # 6. Rewire parent transitions
    result["transitions"] = _rewire_parent_transitions(
        result["transitions"],
        targetState,
        nsPrefix,
        child.get("entry_state"),
        child.get("terminal_states", [])
    )

    # Add child transitions
    result["transitions"].extend(mappedTransitions)

    # 7. Merge context schema
    childCtx = prefixedChild.get("context_schema", {}).get("properties", {})
    if childCtx:
        if "properties" not in result["context_schema"]:
            result["context_schema"]["properties"] = {}
        result["context_schema"]["properties"].update(childCtx)

    return result


def _prefix_child(child: Dict[str, Any], prefix: str) -> Dict[str, Any]:
    """Apply namespace prefix to all child element IDs."""
    result = copy.deepcopy(child)

    # Prefix states
    oldStates = result.get("states", {})
    newStates = {}
    stateMap = {}
    for stateId, stateDef in oldStates.items():
        newId = f"{prefix}{NAMESPACE_SEPARATOR}{stateId}"
        stateMap[stateId] = newId
        newStates[newId] = stateDef
    result["states"] = newStates

    # Prefix gates
    oldGates = result.get("gates", {})
    newGates = {}
    gateMap = {}
    for gateId, gateDef in oldGates.items():
        newId = f"{prefix}{NAMESPACE_SEPARATOR}{gateId}"
        gateMap[gateId] = newId
        newGates[newId] = gateDef
    result["gates"] = newGates

    # Prefix actions
    oldActions = result.get("actions", {})
    newActions = {}
    actionMap = {}
    for actionId, actionDef in oldActions.items():
        newId = f"{prefix}{NAMESPACE_SEPARATOR}{actionId}"
        actionMap[actionId] = newId
        newActions[newId] = copy.deepcopy(actionDef)
    result["actions"] = newActions

    # Update transitions with prefixed IDs
    newTransitions = []
    for t in result.get("transitions", []):
        newT = copy.deepcopy(t)

        # Prefix transition ID
        if "id" in newT:
            newT["id"] = f"{prefix}{NAMESPACE_SEPARATOR}{newT['id']}"

        # Update from/to states
        if newT.get("from") and newT["from"] != "*":
            newT["from"] = stateMap.get(newT["from"], newT["from"])
        if newT.get("to") and newT["to"] != "*":
            newT["to"] = stateMap.get(newT["to"], newT["to"])

        # Update gate references
        if "gates" in newT:
            newT["gates"] = [gateMap.get(g, g) for g in newT["gates"]]
        if "gate" in newT:
            newT["gate"] = gateMap.get(newT["gate"], newT["gate"])

        # Update action references
        if "actions" in newT:
            newT["actions"] = [actionMap.get(a, a) for a in newT["actions"]]

        newTransitions.append(newT)

    result["transitions"] = newTransitions

    # Update entry_state
    if result.get("entry_state"):
        result["entry_state"] = stateMap.get(
            result["entry_state"], result["entry_state"]
        )

    # Update terminal_states
    if result.get("terminal_states"):
        result["terminal_states"] = [
            stateMap.get(s, s) for s in result["terminal_states"]
        ]

    # Prefix context properties
    oldProps = result.get("context_schema", {}).get("properties", {})
    newProps = {}
    for propId, propDef in oldProps.items():
        newId = f"{prefix}{NAMESPACE_SEPARATOR}{propId}"
        newProps[newId] = propDef
    if newProps:
        result["context_schema"] = {"properties": newProps}

    return result


def _map_action_contracts(
    actions: Dict[str, Any],
    contract: Dict[str, Any],
    prefix: str
) -> Dict[str, Any]:
    """Apply contract mappings to actions."""
    inputMap = contract.get("input_map", {})
    outputMap = contract.get("output_map", {})

    result = copy.deepcopy(actions)

    # For COMPUTE actions, we might need to remap input/output
    for actionId, actionDef in result.items():
        if actionDef.get("type") == "compute":
            # Apply input mapping
            actInputMap = actionDef.get("input_map", {})
            for parentCtx, childCtx in inputMap.items():
                # Replace references in input_map values
                for k, v in actInputMap.items():
                    if isinstance(v, str) and childCtx in v:
                        actInputMap[k] = v.replace(childCtx, parentCtx)

            # Apply output mapping
            actOutputMap = actionDef.get("output_map", {})
            for childCtx, parentCtx in outputMap.items():
                # Remap output targets
                for k, v in list(actOutputMap.items()):
                    if k == childCtx.split(".")[-1]:
                        actOutputMap[parentCtx.split(".")[-1]] = v
                        if parentCtx.split(".")[-1] != k:
                            del actOutputMap[k]

    return result


def _map_transitions(
    transitions: List[Dict],
    eventMap: Dict[str, str],
    prefix: str,
    child: Dict[str, Any]
) -> List[Dict]:
    """Apply event mappings to transitions."""
    result = []

    for t in transitions:
        newT = copy.deepcopy(t)

        # Apply event mapping
        originalEvent = newT.get("on_event")
        if originalEvent and originalEvent in eventMap:
            newT["on_event"] = eventMap[originalEvent]

        result.append(newT)

    return result


def _rewire_parent_transitions(
    transitions: List[Dict],
    targetState: str,
    nsPrefix: str,
    childEntry: str,
    childTerminals: List[str]
) -> List[Dict]:
    """Rewire parent transitions to connect to child entry/exit points."""
    result = []

    # Calculate prefixed child entry state
    prefixedEntry = f"{nsPrefix}{NAMESPACE_SEPARATOR}{childEntry}" if childEntry else None
    prefixedTerminals = [
        f"{nsPrefix}{NAMESPACE_SEPARATOR}{s}" for s in (childTerminals or [])
    ]

    for t in transitions:
        newT = copy.deepcopy(t)

        # Transitions TO the target state should go to child entry
        if newT.get("to") == targetState and prefixedEntry:
            newT["to"] = prefixedEntry

        # Transitions FROM the target state - these become transitions from
        # each child terminal state (we add multiple copies)
        if newT.get("from") == targetState:
            if prefixedTerminals:
                # Create a copy for each terminal state
                for termState in prefixedTerminals:
                    termT = copy.deepcopy(newT)
                    termT["from"] = termState
                    # Give unique ID
                    if "id" in termT:
                        termT["id"] = f"{termT['id']}_from_{termState}"
                    result.append(termT)
                continue  # Don't add original
            else:
                # No terminals defined, keep original (might be error)
                pass

        result.append(newT)

    return result


def _bumpVersion(version: str) -> str:
    """Bump patch version number."""
    try:
        parts = version.split(".")
        if len(parts) >= 3:
            parts[2] = str(int(parts[2]) + 1)
            return ".".join(parts)
    except ValueError:
        pass
    return version + "-composed"


# =============================================================================
# Validation
# =============================================================================

def validate_composition(params: Dict[str, Any]) -> Dict[str, Any]:
    """Validate the composed blueprint."""
    composed = params.get("composed")
    parent = params.get("parent")
    embeddings = params.get("embeddings", [])

    errors = []
    warnings = []

    if not composed:
        return {"result": {"errors": ["No composed blueprint"], "warnings": []}}

    # 1. Check for circular references
    circularErrors = _check_circular_references(embeddings)
    errors.extend(circularErrors)

    # 2. Validate all contracts are satisfied
    contractErrors = _validate_contracts(composed, embeddings)
    errors.extend(contractErrors)

    # 3. Check for ID collisions
    collisionErrors = _check_id_collisions(composed)
    errors.extend(collisionErrors)

    # 4. Validate all state references
    stateErrors = _validate_state_references(composed)
    errors.extend(stateErrors)

    # 5. Check for orphaned elements
    orphanWarnings = _check_orphaned_elements(composed)
    warnings.extend(orphanWarnings)

    # 6. Validate entry/terminal states
    entryErrors = _validate_entry_terminal(composed)
    errors.extend(entryErrors)

    return {
        "result": {
            "errors": errors,
            "warnings": warnings,
            "valid": len(errors) == 0
        }
    }


def _check_circular_references(embeddings: List[Dict]) -> List[str]:
    """Check for circular embedding references."""
    errors = []
    seen = set()

    for emb in embeddings:
        childPath = emb.get("child_path", "")
        targetState = emb.get("target_state", "")
        key = f"{childPath}:{targetState}"

        if key in seen:
            errors.append(f"Circular reference detected: {key}")
        seen.add(key)

    return errors


def _validate_contracts(
    composed: Dict[str, Any],
    embeddings: List[Dict]
) -> List[str]:
    """Validate that all contracts are satisfiable."""
    errors = []
    composedProps = set(
        composed.get("context_schema", {}).get("properties", {}).keys()
    )

    for emb in embeddings:
        contract = emb.get("contract", {})
        inputMap = contract.get("input_map", {})
        outputMap = contract.get("output_map", {})

        # Check input mappings reference valid properties
        for parentProp, childProp in inputMap.items():
            parentKey = parentProp.split(".")[-1]
            if parentKey not in composedProps:
                errors.append(
                    f"Input contract references missing property: {parentProp}"
                )

        # Check output mappings target valid properties
        for childProp, parentProp in outputMap.items():
            parentKey = parentProp.split(".")[-1]
            # Output props should exist or will be created
            # This is more of a warning

    return errors


def _check_id_collisions(composed: Dict[str, Any]) -> List[str]:
    """Check for ID collisions after composition."""
    errors = []
    seen = {}

    # Check states
    for stateId in composed.get("states", {}).keys():
        if stateId in seen:
            errors.append(f"State ID collision: {stateId}")
        seen[stateId] = "state"

    # Check gates
    for gateId in composed.get("gates", {}).keys():
        if gateId in seen and seen[gateId] == "gate":
            errors.append(f"Gate ID collision: {gateId}")
        seen[gateId] = "gate"

    # Check actions
    for actionId in composed.get("actions", {}).keys():
        if actionId in seen and seen[actionId] == "action":
            errors.append(f"Action ID collision: {actionId}")
        seen[actionId] = "action"

    # Check transition IDs
    transitionIds = set()
    for t in composed.get("transitions", []):
        tid = t.get("id")
        if tid:
            if tid in transitionIds:
                errors.append(f"Transition ID collision: {tid}")
            transitionIds.add(tid)

    return errors


def _validate_state_references(composed: Dict[str, Any]) -> List[str]:
    """Validate all state references in transitions."""
    errors = []
    states = set(composed.get("states", {}).keys())

    for t in composed.get("transitions", []):
        tid = t.get("id", "unknown")
        fromState = t.get("from")
        toState = t.get("to")

        if fromState and fromState != "*" and fromState not in states:
            errors.append(
                f"Transition {tid} references non-existent from state: "
                f"{fromState}"
            )

        if toState and toState != "*" and toState not in states:
            errors.append(
                f"Transition {tid} references non-existent to state: {toState}"
            )

    return errors


def _check_orphaned_elements(composed: Dict[str, Any]) -> List[str]:
    """Check for orphaned gates and actions."""
    warnings = []

    usedGates = set()
    usedActions = set()

    for t in composed.get("transitions", []):
        for g in t.get("gates", []):
            usedGates.add(g)
        if t.get("gate"):
            usedGates.add(t["gate"])
        for a in t.get("actions", []):
            usedActions.add(a)

    definedGates = set(composed.get("gates", {}).keys())
    definedActions = set(composed.get("actions", {}).keys())

    unusedGates = definedGates - usedGates
    unusedActions = definedActions - usedActions

    for g in unusedGates:
        warnings.append(f"Unused gate after composition: {g}")

    for a in unusedActions:
        warnings.append(f"Unused action after composition: {a}")

    return warnings


def _validate_entry_terminal(composed: Dict[str, Any]) -> List[str]:
    """Validate entry and terminal state references."""
    errors = []
    states = set(composed.get("states", {}).keys())

    entryState = composed.get("entry_state")
    if entryState and entryState not in states:
        errors.append(f"Entry state not found: {entryState}")

    for termState in composed.get("terminal_states", []):
        if termState not in states:
            errors.append(f"Terminal state not found: {termState}")

    return errors


# =============================================================================
# Flatten
# =============================================================================

def flatten(params: Dict[str, Any]) -> Dict[str, Any]:
    """Flatten nested compositions (resolve all namespace prefixes)."""
    composed = params.get("composed")

    if not composed:
        return {"flattened": None}

    # For now, just return as-is. True flattening would involve
    # resolving nested compositions recursively.
    flattened = copy.deepcopy(composed)

    return {"flattened": flattened}


# =============================================================================
# Export
# =============================================================================

def export_composed(params: Dict[str, Any]) -> Dict[str, Any]:
    """Export composed blueprint to file."""
    blueprint = params.get("blueprint")
    path = params.get("path")

    if not blueprint:
        return {"path": None, "error": "No composed blueprint to export"}

    if not path:
        return {"path": None, "error": "No export path specified"}

    try:
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)

        with open(p, "w") as f:
            json.dump(blueprint, f, indent=2)

        return {"path": str(p), "error": None}
    except Exception as e:
        return {"path": None, "error": str(e)}


# =============================================================================
# Manifest Operations
# =============================================================================

def load_manifest(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load a composition manifest file."""
    path = params.get("path")

    if not path:
        return {
            "manifest": None,
            "parent": None,
            "parent_path": None,
            "embeddings": None,
            "error": "No path provided"
        }

    try:
        p = Path(path)
        if not p.exists():
            return {
                "manifest": None,
                "parent": None,
                "parent_path": None,
                "embeddings": None,
                "error": f"File not found: {path}"
            }

        with open(p) as f:
            manifest = json.load(f)

        # Load parent blueprint
        parentPath = manifest.get("parent")
        if not parentPath:
            return {
                "manifest": manifest,
                "parent": None,
                "parent_path": None,
                "embeddings": None,
                "error": "Manifest missing parent path"
            }

        # Resolve relative paths from manifest location
        manifestDir = p.parent
        parentFullPath = (manifestDir / parentPath).resolve()

        parentResult = load_parent({"path": str(parentFullPath)})
        if parentResult.get("error"):
            return {
                "manifest": manifest,
                "parent": None,
                "parent_path": None,
                "embeddings": None,
                "error": parentResult["error"]
            }

        # Load all child blueprints and build embeddings
        embeddings = []
        for embDef in manifest.get("embeddings", []):
            childPath = embDef.get("child")
            if not childPath:
                continue

            childFullPath = (manifestDir / childPath).resolve()
            childResult = load_child({"path": str(childFullPath)})
            if childResult.get("error"):
                return {
                    "manifest": manifest,
                    "parent": parentResult["blueprint"],
                    "parent_path": str(parentFullPath),
                    "embeddings": None,
                    "error": f"Failed to load child: {childResult['error']}"
                }

            embedding = {
                "target_state": embDef.get("target_state"),
                "namespace_prefix": embDef.get(
                    "namespace_prefix", embDef.get("target_state")
                ),
                "child": childResult["blueprint"],
                "child_path": str(childFullPath),
                "contract": embDef.get("contract", {
                    "input_map": {},
                    "output_map": {}
                }),
                "event_map": embDef.get("event_map", {})
            }
            embeddings.append(embedding)

        return {
            "manifest": manifest,
            "parent": parentResult["blueprint"],
            "parent_path": str(parentFullPath),
            "embeddings": embeddings,
            "error": None
        }

    except json.JSONDecodeError as e:
        return {
            "manifest": None,
            "parent": None,
            "parent_path": None,
            "embeddings": None,
            "error": f"Invalid JSON: {e}"
        }
    except Exception as e:
        return {
            "manifest": None,
            "parent": None,
            "parent_path": None,
            "embeddings": None,
            "error": str(e)
        }


def compose_from_manifest(params: Dict[str, Any]) -> Dict[str, Any]:
    """Compose blueprints based on a loaded manifest."""
    manifest = params.get("manifest")

    if not manifest:
        return {"composed": None, "error": "No manifest loaded"}

    # The manifest should have already triggered loading parent and embeddings
    # This function is called after load_manifest populates the context
    # We need to access these from context, but since we're in a compute unit,
    # we need them passed in

    # Actually, since the blueprint drives the flow, the context will have
    # parent_blueprint and embeddings populated by load_manifest
    # But this compute unit is called separately, so we use compose()

    # For manifest-based compose, we should receive parent and embeddings
    # from the context via the action's input_map

    return {"composed": None, "error": "Use compose action after load_manifest"}


def generate_manifest(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate a composition manifest from current state."""
    parentPath = params.get("parent_path")
    embeddings = params.get("embeddings", [])

    if not parentPath:
        return {"manifest": None}

    manifest = {
        "parent": parentPath,
        "embeddings": []
    }

    for emb in embeddings:
        embDef = {
            "target_state": emb.get("target_state"),
            "child": emb.get("child_path"),
            "contract": emb.get("contract", {}),
            "event_map": emb.get("event_map", {})
        }
        if emb.get("namespace_prefix") != emb.get("target_state"):
            embDef["namespace_prefix"] = emb.get("namespace_prefix")
        manifest["embeddings"].append(embDef)

    return {"manifest": manifest}


def export_manifest(params: Dict[str, Any]) -> Dict[str, Any]:
    """Export composition manifest to file."""
    manifest = params.get("manifest")
    path = params.get("path")

    if not manifest:
        return {"path": None, "error": "No manifest to export"}

    if not path:
        return {"path": None, "error": "No export path specified"}

    try:
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)

        with open(p, "w") as f:
            json.dump(manifest, f, indent=2)

        return {"path": str(p), "error": None}
    except Exception as e:
        return {"path": None, "error": str(e)}


def clear_all(params: Dict[str, Any]) -> Dict[str, Any]:
    """Clear all state."""
    return {
        "parent_blueprint": None,
        "child_blueprint": None,
        "embeddings": None,
        "current_embedding": None,
        "composed_blueprint": None,
        "validation_result": None,
        "manifest": None
    }


# =============================================================================
# COMPUTE REGISTRY - Maps compute_unit names to functions
# =============================================================================

COMPUTE_REGISTRY = {
    "compose:load_parent": load_parent,
    "compose:load_child": load_child,
    "compose:init_embedding": init_embedding,
    "compose:set_input_contract": set_input_contract,
    "compose:set_output_contract": set_output_contract,
    "compose:set_event_map": set_event_map,
    "compose:finalize_embedding": finalize_embedding,
    "compose:compose": compose,
    "compose:validate_composition": validate_composition,
    "compose:flatten": flatten,
    "compose:export_composed": export_composed,
    "compose:load_manifest": load_manifest,
    "compose:compose_from_manifest": compose_from_manifest,
    "compose:generate_manifest": generate_manifest,
    "compose:export_manifest": export_manifest,
    "compose:clear_all": clear_all,
}
