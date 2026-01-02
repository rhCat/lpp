#!/usr/bin/env python3
"""Run TLAPS Seal certification on all core L++ blueprints."""
from src.seal_compute import (loadBlueprint, auditTrinity, auditFlange,
                              generateTla, runTlc, runTlaps, generateCertificate)
import json
import os
from pathlib import Path
from datetime import datetime

# Core blueprints to certify
BLUEPRINTS = [
    '../../src/blueprints/core_jsons/loader_blueprint.json',
    '../../src/blueprints/core_jsons/schema_blueprint.json',
    '../../src/blueprints/core_jsons/orchestrator_blueprint.json',
    '../../src/blueprints/core_jsons/validator_blueprint.json',
    '../../src/blueprints/core_jsons/lpp_core_blueprint.json',
    '../../src/blueprints/core_jsons/safe_eval_blueprint.json',
    '../../src/blueprints/core_jsons/tla_validator_blueprint.json',
    '../../src/blueprints/core_jsons/visualizer_blueprint.json',
    '../../src/blueprints/core_jsons/compiler_blueprint.json',
]


def main():
    # Output directory for seals
    seal_dir = Path('../../src/frame_py/tlaps_seals/v0')
    seal_dir.mkdir(parents=True, exist_ok=True)

    all_certs = []

    for bp_path in BLUEPRINTS:
        name = os.path.basename(bp_path).replace('_blueprint.json', '')
        print(f'\n{"="*60}')
        print(f'Certifying: {name}')
        print('='*60)

        # Load
        load_result = loadBlueprint({'blueprintPath': bp_path})
        if load_result.get('error'):
            print(f'LOAD ERROR: {load_result["error"]}')
            continue
        bp = load_result['blueprint']

        # Audit Trinity
        trinity = auditTrinity({'blueprint': bp})
        t_audit = trinity['trinityAudit']
        print(
            f'Trinity: T={t_audit["transitions"]["count"]} G={t_audit["gates"]["count"]} A={t_audit["actions"]["count"]}')

        # Audit Flange
        flange = auditFlange({'blueprint': bp})
        f_audit = flange['flangeAudit']
        print(
            f'Flange: props={f_audit["properties"]["count"]} hermeticity={f_audit["hermeticity"]["score"]:.2f}')

        # Generate TLA+
        tla_result = generateTla({'blueprint': bp, 'blueprintPath': bp_path})
        if tla_result.get('tlaPath'):
            print(f'TLA+ generated: {tla_result["tlaPath"]}')

        # Run TLC
        tlc_result = runTlc({'tlaPath': tla_result.get('tlaPath')})
        tlc = tlc_result.get('tlcResult', {})
        print(
            f'TLC: passed={tlc.get("passed")} states={tlc.get("statesExplored", 0)}')

        # Run TLAPS (or simulate)
        tlaps_result = runTlaps({'tlaPath': tla_result.get('tlaPath')})
        tlaps = tlaps_result.get('tlapsResult', {})
        print(
            f'TLAPS: passed={tlaps.get("passed")} theorems={list(tlaps.get("theorems", {}).keys())}')

        # Generate Certificate
        cert_result = generateCertificate({
            'blueprint': bp,
            'trinityAudit': t_audit,
            'flangeAudit': f_audit,
            'tlcResult': tlc,
            'tlapsResult': tlaps
        })
        cert = cert_result['sealCertificate']
        print(f'SEAL: {cert["seal"]} | Level: {cert["level"]}')

        # Save certificate
        cert_path = seal_dir / f'{name}_seal.json'
        with open(cert_path, 'w') as f:
            json.dump(cert, f, indent=2)
        print(f'Certificate saved: {cert_path}')

        all_certs.append(cert)

    # Generate summary log
    log_lines = [
        '# TLAPS Seal Log - L++ Core Components v0',
        '',
        '**Formal Verification Certificates for L++ Core**',
        '',
        f'Generated: {datetime.utcnow().isoformat()}Z',
        '',
        '---',
        '',
        '## Summary',
        '',
        '| Blueprint | Version | Seal | Level | Hash |',
        '|-----------|---------|------|-------|------|',
    ]

    for cert in all_certs:
        bp_info = cert['blueprint']
        log_lines.append(
            f'| {bp_info["id"]} | {bp_info["version"]} | {cert["seal"]} | {cert["level"]} | `{bp_info["hash"][:16]}` |'
        )

    log_lines.extend([
        '',
        '---',
        '',
        '## The Engineering Oath',
        '',
        'Each certified component adheres to:',
        '',
        '- The Logic is Converged: No path leads to unhandled deadlock.',
        '- The Context is Hermetic: No data violates schema boundaries.',
        '- The Flesh is Governed: Volatile compute is bound by bone.',
        '',
    ])

    # Save log
    log_path = seal_dir / 'seal_log.md'
    with open(log_path, 'w') as f:
        f.write('\n'.join(log_lines))

    # Print summary
    print('\n' + '='*60)
    print('SEAL LOG SUMMARY')
    print('='*60)
    print(f'Generated: {datetime.utcnow().isoformat()}Z')
    print()
    print('| Blueprint | Version | Seal | Level | Hash |')
    print('|-----------|---------|------|-------|------|')
    for cert in all_certs:
        bp_info = cert['blueprint']
        print(
            f'| {bp_info["id"]} | {bp_info["version"]} | {cert["seal"]} | {cert["level"]} | {bp_info["hash"][:16]} |')

    print(f'\nSeal log saved: {log_path}')


if __name__ == '__main__':
    main()
