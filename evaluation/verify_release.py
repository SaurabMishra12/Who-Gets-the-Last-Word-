"""Check file integrity, allowed formats and nonempty released request/output schemas."""
import hashlib
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
manifest=json.loads((root/'provenance/release_sha256.json').read_text())
files={str(p.relative_to(root)):p for p in root.rglob('*') if p.is_file() and '.git' not in p.parts and '__pycache__' not in p.parts and p.name!='release_sha256.json'}
if set(files)!=set(manifest):raise ValueError('File inventory mismatch')
for name,p in files.items():
    if p.suffix not in {'.json','.csv','.tex','.py','.lean','.ipynb'}:raise ValueError('Unexpected format: '+name)
    if hashlib.sha256(p.read_bytes()).hexdigest()!=manifest[name]:raise ValueError('Hash mismatch: '+name)
    if p.suffix=='.json':json.loads(p.read_text())
requests=0;completions=0
for p in (root/'prompts/instantiated').rglob('*.json'):
    for r in json.loads(p.read_text()):
        if not isinstance(r['messages'],list) or len(r['messages'])<2:raise ValueError('Missing saved messages: '+str(p))
        if any(not isinstance(m['content'],str) for m in r['messages']):raise ValueError('Invalid message')
        requests+=1
for p in (root/'raw_outputs').rglob('completions.json'):
    for r in json.loads(p.read_text()):
        if not r['choices']:raise ValueError('Missing raw choices: '+str(p))
        completions+=1
print(json.dumps({'status':'PASS','files':len(files),'saved_requests':requests,'saved_completions':completions}))
