"""CI selection includes changed papers and former or transitive consumers."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from scripts.ci_change_scope import plan, prune_build_cache, require_clean_head, successful_main_base


class ScopeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.org")
        self.write("lakefile.toml", 'name="Fixture"\n' + '\n'.join(
            f'[[lean_lib]]\nname="{name}"\n' + ('srcDir="papers"\n' if name != 'AppliedModelingLib' else '')
            for name in ('AppliedModelingLib', 'AAA24Paper', 'BBB24Paper', 'CCC24Paper', 'DDD24Paper')))
        self.write('AppliedModelingLib.lean', '-- Library\n')
        for paper in ('AAA24Paper', 'BBB24Paper', 'CCC24Paper', 'DDD24Paper'):
            self.write(f'papers/{paper}/status.json', '{}\n')
            self.write(f'papers/{paper}.lean', f'import {paper}.Main\n')
            self.write(f'papers/{paper}/Main.lean', '-- Proofs\n')
        self.write('papers/BBB24Paper/Main.lean', 'import AAA24Paper.Main\n')
        self.write('papers/CCC24Paper/Main.lean', 'import BBB24Paper.Main\n')
        self.commit()
        self.git('tag', 'base')

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.root), *args], stderr=subprocess.DEVNULL)

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def commit(self):
        self.git('add', '--all')
        self.git('commit', '-qm', 'fixture')

    def successful_run(self, sha):
        return dict(status='completed', conclusion='success', event='push',
                    head_branch='main', head_sha=sha,
                    path='.github/workflows/lean_action_ci.yml',
                    head_repository={'full_name': 'Owner/Repo'})

    def test_docs_followup_still_checks_prior_unvalidated_proof_change(self):
        base = self.git('rev-parse', 'base').decode().strip()
        self.write('papers/AAA24Paper/Main.lean', '-- Changed proof\n')
        self.commit()
        unfinished = self.git('rev-parse', 'HEAD').decode().strip()
        self.write('docs/readme.md', '# Documentation follow-up\n')
        self.commit()
        failed = self.successful_run(unfinished)
        failed['conclusion'] = 'cancelled'
        selected = successful_main_base(self.root, 'HEAD',
            {'workflow_runs': [failed, self.successful_run(base)]}, 'Owner/Repo')
        self.assertEqual(selected, base)
        # A mixed proof/documentation diff conservatively takes the full lane.
        self.assertEqual(plan(self.root, selected)['mode'], 'integration')
        self.assertEqual(plan(self.root, unfinished)['mode'], 'docs')

    def test_successful_baseline_is_the_newest_validated_ancestor(self):
        old = self.git('rev-parse', 'HEAD').decode().strip()
        self.write('docs/a.md', 'First documentation change\n')
        self.commit()
        newer = self.git('rev-parse', 'HEAD').decode().strip()
        self.write('docs/b.md', 'Second documentation change\n')
        self.commit()
        runs = {'workflow_runs': [self.successful_run(newer), self.successful_run(old)]}
        self.assertEqual(successful_main_base(self.root, 'HEAD', runs, 'Owner/Repo'), newer)
        self.assertEqual(plan(self.root, newer)['mode'], 'docs')

    def test_no_untrusted_run_can_supply_a_main_baseline(self):
        sha = self.git('rev-parse', 'HEAD').decode().strip()
        for key, value in [('event', 'pull_request'), ('status', 'in_progress'),
                           ('head_branch', 'other'), ('conclusion', 'failure'),
                           ('path', '.github/workflows/pages.yml'),
                           ('head_sha', '0' * 40),
                           ('head_repository', {'full_name': 'Other/Repo'})]:
            row = self.successful_run(sha); row[key] = value
            with self.subTest(key=key):
                self.assertEqual(successful_main_base(self.root, 'HEAD',
                    {'workflow_runs': [row]}, 'Owner/Repo'), '')

    def test_restored_cache_keeps_live_modules_and_removes_deleted_interfaces(self):
        self.write('.lake/build/lib/lean/AAA24Paper/Main.olean', 'live compiled module')
        self.write('.lake/build/lib/lean/Removed/Main.olean', 'obsolete compiled module')
        self.write('.lake/build/lib/lean/Removed/Main.olean.private', 'obsolete private data')
        prune_build_cache(self.root, 'HEAD')
        self.assertTrue((self.root / '.lake/build/lib/lean/AAA24Paper/Main.olean').exists())
        self.assertFalse((self.root / '.lake/build/lib/lean/Removed/Main.olean').exists())
        self.assertFalse((self.root / '.lake/build/lib/lean/Removed/Main.olean.private').exists())

    def test_build_refuses_uncommitted_lean_inputs(self):
        head = self.git('rev-parse', 'HEAD').decode().strip()
        self.write('papers/AAA24Paper/Untracked.lean', '-- Hidden input')
        with self.assertRaisesRegex(ValueError, 'Untracked Lean'):
            require_clean_head(self.root, head)

    def test_website_only_skips_lean(self):
        self.write('site/index.html', '<h1>Project</h1>')
        self.commit()
        self.assertEqual(plan(self.root, 'base')['mode'], 'docs')

    def test_aggregate_projection_also_skips_lean(self):
        self.write('papers/status.json', '{}\n')
        self.commit()
        self.assertEqual(plan(self.root, 'base')['mode'], 'docs')

    def test_multiple_papers_and_transitive_dependents(self):
        self.write('papers/AAA24Paper/Main.lean', '-- Updated theorem\n')
        self.write('papers/DDD24Paper/Main.lean', '-- Another theorem\n')
        self.commit()
        result = plan(self.root, 'base')
        self.assertEqual(result['mode'], 'papers')
        self.assertEqual(result['targets'], ['AAA24Paper', 'BBB24Paper', 'CCC24Paper', 'DDD24Paper'])

    def test_deleted_module_and_former_dependency_are_checked(self):
        (self.root / 'papers/AAA24Paper/Main.lean').unlink()
        self.write('papers/BBB24Paper/Main.lean', '-- Former dependency removed\n')
        self.commit()
        self.assertEqual(plan(self.root, 'base')['targets'], ['AAA24Paper', 'BBB24Paper', 'CCC24Paper'])

    def test_report_only_checks_its_paper_without_compilation(self):
        self.write('papers/AAA24Paper/FINAL_VALIDATION_REPORT.md', '# Report\n')
        self.commit()
        result = plan(self.root, 'base')
        self.assertEqual(result['papers'], ['AAA24Paper'])
        self.assertEqual(result['targets'], [])

    def test_shared_build_and_tooling_changes_stay_broad(self):
        for path in ('AppliedModelingLib.lean', 'lean-toolchain', 'scripts/audit.py', 'docs/Unexpected.lean'):
            with self.subTest(path=path):
                self.write(path, '-- Changed\n')
                self.commit()
                self.assertEqual(plan(self.root, 'base')['mode'], 'integration')

    def test_custom_registered_consumer_forces_broader_validation(self):
        with (self.root / 'lakefile.toml').open('a') as stream:
            stream.write('\n[[lean_lib]]\nname="FixtureAudit"\nsrcDir="scripts"\nroots=["fixture_helper"]\n')
        self.write('scripts/fixture_helper.lean', 'import AAA24Paper.Main\n')
        self.commit()
        self.git('tag', '-f', 'base')
        self.write('papers/AAA24Paper/Main.lean', '-- Changed premise\n')
        self.commit()
        self.assertEqual(plan(self.root, 'base')['mode'], 'integration')

    def test_worktree_edits_cannot_change_committed_selection(self):
        self.write('site/index.html', '<h1>Project</h1>')
        self.commit()
        self.write('AppliedModelingLib.lean', '-- Uncommitted source edit\n')
        self.assertEqual(plan(self.root, 'base')['mode'], 'docs')


if __name__ == '__main__':
    unittest.main()
