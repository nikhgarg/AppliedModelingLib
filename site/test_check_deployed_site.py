import tempfile
from pathlib import Path
import unittest
from unittest.mock import patch

from check_deployed_site import check, check_legacy, local_links


class DeployedSiteTests(unittest.TestCase):
    def test_checks_linked_memo_anchor_and_pdf(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / 'index.html').write_text('<a href="memo.html#detail">Memo</a>')
            (root / 'memo.html').write_text('<h2 id="detail">Detail</h2><a href="dag.pdf">DAG</a>')
            (root / 'dag.pdf').write_bytes(b'%PDF-test')
            self.assertEqual(set(local_links(root, 'https://example.org/project/')), {'index.html', 'memo.html', 'dag.pdf'})
            (root / 'memo.html').write_text('<h2 id="changed">Changed</h2>')
            with self.assertRaisesRegex(ValueError, 'missing anchor'):
                local_links(root, 'https://example.org/project/')

    @patch('check_deployed_site.time.sleep')
    def test_old_deployment_cannot_pass(self, _):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / 'index.html').write_text('current release')
            with self.assertRaisesRegex(RuntimeError, 'Deployed bytes differ'):
                check(root, 'https://example.org/project/', fetcher=lambda url: (url, b'old release'))

    def test_legacy_url_text_alone_is_not_a_redirect(self):
        with self.assertRaisesRegex(ValueError, 'does not redirect'):
            check_legacy('https://example.org/AppliedModelingLib/', fetcher=lambda url: (url, b'<p>https://example.org/AppliedModelingLib/</p>'))


if __name__ == '__main__':
    unittest.main()
