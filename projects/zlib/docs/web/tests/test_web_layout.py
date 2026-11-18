"""The reference builder must keep en/ and zh/ trees clean and exclude web code and articles."""
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import reference


class ConsolidatedDocumentation(unittest.TestCase):
    def test_reference_inventory_excludes_web_output_and_main_articles(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for name in [
                'docs/en/overview.md',
                'docs/en/spec/safety.md',
                'docs/en/read/codec.md',
                'docs/zh/overview.md',
                'docs/zh/spec/safety.md',
                'docs/zh/read/codec.md',
                'docs/web/README.md',
                'docs/web/dist/en/copied.md',
            ]:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text('# Document\n')
            with patch.object(reference, 'REPO', root):
                self.assertEqual(
                    [p.relative_to(root).as_posix() for p in reference.documents('en')],
                    ['docs/en/overview.md', 'docs/en/spec/safety.md'],
                )
                self.assertEqual(
                    [p.relative_to(root).as_posix() for p in reference.documents('zh')],
                    ['docs/zh/overview.md', 'docs/zh/spec/safety.md'],
                )

    def test_doc_paths_use_language_prefixes_without_suffixes(self):
        routes = ['read/codec', 'read/optimizations', 'read/features', 'overview', 'spec/safety']
        for route in routes:
            for src_lang in ('en', 'zh'):
                source = reference.REPO / 'docs' / src_lang / (route + '.md')
                for out_lang in ('en', 'zh'):
                    expected = reference.OUT / out_lang / (route + '.html')
                    self.assertEqual(reference.doc_path(source, out_lang), expected)


if __name__ == '__main__':
    unittest.main()
