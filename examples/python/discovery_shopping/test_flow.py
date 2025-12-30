#!/usr/bin/env python3
"""Test flow: real Google Search for shoes"""
import importlib.util
from src import COMPUTE_REGISTRY
from frame_py.compiler import compile_blueprint
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent / 'src'))

# Compile & load
HERE = Path(__file__).parent
out = HERE / 'results/discovery_shopping_compiled.py'
compile_blueprint(str(HERE / 'discovery_shopping.json'), str(out))
spec = importlib.util.spec_from_file_location('op', out)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
reg = {tuple(k.split(':')): fn for k, fn in COMPUTE_REGISTRY.items()}
op = mod.create_operator(reg)

print('🛒 Real Google Search: Finding shoes')
print('='*50)

# 1. Select category
print(f'\n[{op.state}] SELECT_CATEGORY shoes')
op.dispatch('SELECT_CATEGORY', {'category': 'shoes'})
print(f'→ {op.state}')

# 2. Answer quiz for shoes (5 questions)
print(f'\n[{op.state}] ANSWER q1=Running')
op.dispatch('ANSWER', {'question_id': 'q1', 'answer': 'Running'})
print(f'→ {op.state}')

print(f'\n[{op.state}] ANSWER q2=Road')
op.dispatch('ANSWER', {'question_id': 'q2', 'answer': 'Road'})
print(f'→ {op.state}')

print(f'\n[{op.state}] ANSWER q3=Standard')
op.dispatch('ANSWER', {'question_id': 'q3', 'answer': 'Standard'})
print(f'→ {op.state}')

print(f'\n[{op.state}] ANSWER q4=$75-125')
op.dispatch('ANSWER', {'question_id': 'q4', 'answer': '$75-125'})
print(f'→ {op.state}')

print(f'\n[{op.state}] ANSWER q5=Not needed')
op.dispatch('ANSWER', {'question_id': 'q5', 'answer': 'Not needed'})
print(f'→ {op.state}')

# Show fetch progress
ctx = op.context
off = ctx.get('fetch_offset', 0)
tot = ctx.get('fetch_total', 0)
more = ctx.get('has_more_products', False)
print(f'\n📦 Fetched {off}/{tot} products')
print(f'   Has more: {more}')

# Continue to analyzing
print(f'\n[{op.state}] DONE (continue to analyze)')
op.dispatch('DONE', {})
print(f'→ {op.state}')

# Continue to ranking
print(f'\n[{op.state}] DONE (continue to rank)')
op.dispatch('DONE', {})
print(f'→ {op.state}')

# Continue to browsing
print(f'\n[{op.state}] DONE (show results)')
op.dispatch('DONE', {})
print(f'→ {op.state}')

# Show rankings
print(f'\n🏆 Top Results (from Google Search):')
rankings = op.context.get('rankings', [])
if rankings:
    for i, r in enumerate(rankings[:5], 1):
        name = r['product_name']
        price = r['price']
        score = r['score']
        rating = r['rating']
        reason = r['reasons'][0] if r['reasons'] else ''
        print(f'  {i}. {name}')
        print(f'     ${price:.2f} | ⭐{rating:.1f} | score: {score:.2f}')
        print(f'     {reason}')
else:
    print('  No rankings found')
