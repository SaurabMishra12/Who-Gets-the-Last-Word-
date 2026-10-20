"""Build the released Lean project in a temporary directory using an installed toolchain."""
import json
import shutil
import subprocess
import tempfile
from pathlib import Path
root=Path(__file__).resolve().parents[1]/'formal'
config=json.loads((root/'build_config.json').read_text())
with tempfile.TemporaryDirectory(prefix='lastword-lean-') as dest:
    dest=Path(dest)
    for p in root.rglob('*.lean'):
        target=dest/p.relative_to(root);target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,target)
    (dest/'lean-toolchain').write_text(config['lean_toolchain']+'\n')
    (dest/'lakefile.toml').write_text(config['lakefile_toml'])
    subprocess.run(['lake','build'],cwd=dest,check=True)
    subprocess.run(['lake','env','lean','AxiomAudit.lean'],cwd=dest,check=True)
