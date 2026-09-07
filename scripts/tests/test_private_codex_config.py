from __future__ import annotations

import unittest
from pathlib import Path

from scripts.tomllib_compat import tomllib


ROOT = Path(__file__).resolve().parents[2]
CONFIG = ROOT / ".codex" / "config.toml"


class PrivateCodexConfigTests(unittest.TestCase):
    def test_login_shell_startup_noise_is_disabled_project_wide(self) -> None:
        if not CONFIG.is_file():
            self.skipTest("private project Codex configuration is not present")
        payload = tomllib.loads(CONFIG.read_text(encoding="utf-8"))

        self.assertIs(payload.get("allow_login_shell"), False)
        shell_policy = payload.get("shell_environment_policy")
        self.assertIsInstance(shell_policy, dict)
        self.assertEqual(
            shell_policy.get("set", {}).get("SYSTEMD_LOG_TARGET"),
            "null",
        )


if __name__ == "__main__":
    unittest.main()
