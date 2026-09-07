"""The exact trusted archive must load without borrowing candidate config."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class TrustedArchiveTests(unittest.TestCase):
    def test_workflow_archive_can_start_scope_classifier(self):
        workflow = (ROOT / '.github/workflows/lean_action_ci.yml').read_text()
        command = next(line.strip() for line in workflow.splitlines() if line.strip().startswith('git archive "$BASE_SHA"'))
        with tempfile.TemporaryDirectory() as temp:
            environment = {**os.environ, 'BASE_SHA': 'HEAD', 'TRUSTED_CI_ROOT': temp}
            subprocess.run(['bash', '-o', 'pipefail', '-c', command], cwd=ROOT, env=environment, check=True)
            result = subprocess.run(['python3', str(Path(temp) / 'scripts/paper_contribution.py'), 'scope', '--help'], cwd=temp, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('--base', result.stdout)


if __name__ == '__main__':
    unittest.main()
