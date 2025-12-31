#!/usr/bin/env python3
"""Test scholar_chat to learn about TLA+"""
import sys
sys.path.insert(0, '../../src')
sys.path.insert(0, 'src')

from scholar_compute import synthesize, initConfig

config = initConfig({})

tla_context = [
    {
        'title': 'TLA+ Trifecta: TLC, Apalache, TLAPS',
        'abstract': 'TLA+ is a formal specification language for concurrent and distributed systems. TLC is a model checker that exhaustively searches state space. Apalache uses symbolic model checking via SMT solvers. TLAPS is a proof system for mechanized proofs.'
    },
    {
        'title': 'Practical TLA+ by Hillel Wayne',
        'abstract': 'TLA+ uses temporal logic of actions. Key concepts: variables, states, actions (state transitions), behaviors (sequences of states). PlusCal is an algorithm language that compiles to TLA+.'
    },
    {
        'title': 'TLA+ in Industry',
        'abstract': 'Amazon Web Services uses TLA+ to verify distributed systems like S3 and DynamoDB. It found critical bugs that traditional testing missed. Microsoft uses TLA+ for Azure Cosmos DB consistency protocols.'
    }
]

print('=== TLA+ Deep Dive: Core Concepts ===\n')

synth_result = synthesize({
    'query': 'What are the core concepts of TLA+ and how do the tools TLC, Apalache, and TLAPS differ?',
    'paperDetails': tla_context,
    'paperLinks': [{'title': p['title'], 'url': '', 'pdfUrl': ''} for p in tla_context],
    'apiKey': config['apiKey'],
    'apiBase': config['apiBase'],
    'model': config['model']
})

if synth_result.get('error'):
    print(f'Error: {synth_result["error"]}')
else:
    print(synth_result.get('synthesis', ''))
    print()
    for q in synth_result.get('followUpQuestions', [])[:3]:
        print(f'-> {q}')
