#!/usr/bin/env python3
"""Negative and reproduction checks for this library's native API adapter."""

import copy
import json
import os
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch

import generate_api as api


class HeaderChecks(unittest.TestCase):
    def test_visible_tokens_and_entities(self):
        value = ('<div class="decl_header"><span class="decl_kind">noncomputable def</span>'
                 ' <span class="decl_name">Foo.bar</span> {A : Type u}'
                 '<div class="decl_type">A &lt; B ∧ A ≤ B</div></div>')
        parsed = api.Header(value)
        self.assertEqual(parsed.rendered(),
                         'noncomputable def Foo.bar {A : Type u} A < B ∧ A ≤ B')
        self.assertEqual(''.join(parsed.names), 'Foo.bar')
        self.assertEqual(''.join(parsed.kinds), 'noncomputable def')

    def test_malformed_header_refused(self):
        for value in ('<script>evil</script>', '<div><span></div>',
                      '<div>unclosed', '<span onclick="x">bad</span>',
                      '<div><!--unknown--></div>', '<!DOCTYPE html>', 'outside'):
            with self.subTest(value=value), self.assertRaises(ValueError):
                api.Header(value)

    def test_nested_structure_and_class_sites(self):
        page = (b'<div class="decl" id="Foo">'
                b'<ul class="structure_fields" id="Foo.mk">'
                b'<li class="structure_field" id="Foo.member">'
                b'<div class="structure_field_info">member : Nat</div></li></ul></div>')
        sites = api.SiteParser(page)
        self.assertEqual(sites.declarations, {'Foo'})
        self.assertEqual({site['name'] for site in sites.sites}, {'Foo.mk', 'Foo.member'})
        self.assertEqual({site['parent'] for site in sites.sites}, {'Foo'})


class NativeChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        directory = os.getenv('SHEAF_NATIVE_DATA')
        html_root = os.getenv('SHEAF_HTML_ROOT')
        if not directory or not html_root:
            raise unittest.SkipTest('set SHEAF_NATIVE_DATA and SHEAF_HTML_ROOT for integration checks')
        cls.records = api.load_native(Path(directory))
        cls.html_root = Path(html_root)
        cls.sources = {path: (api.ROOT / path).read_bytes() for path in api.INPUTS}

    def test_fixed_immutable_complete_inventory(self):
        observed, page_hashes = api.observe(self.records, self.html_root, self.sources)
        self.assertEqual(observed, json.loads(api.INVENTORY.read_bytes()))
        self.assertEqual(set(page_hashes), set(api.MODULES))
        markdown, raw_manifest = api.render(self.records, self.html_root, self.sources)
        manifest = json.loads(raw_manifest)
        self.assertEqual(markdown, (api.ROOT / 'docs/API.md').read_bytes())
        self.assertEqual(raw_manifest, (api.ROOT / 'docs/api-manifest.json').read_bytes())
        self.assertFalse(manifest['proof_certification'])
        self.assertEqual(manifest['modules'], list(api.MODULES))
        self.assertEqual(manifest['display_sites'], len(observed))

    def test_local_instance_source_spans_and_only_twelve_annotated_rows(self):
        sites = api.local_instance_sites(self.records, self.sources)
        self.assertEqual(len(sites), 12)
        markdown, _ = api.render(self.records, self.html_root, self.sources)
        sections = re.split(r'(?=^<a id="api-[0-9a-f]{16}"></a>$)',
                            markdown.decode(), flags=re.MULTILINE)[1:]
        by_name = {}
        for section in sections:
            match = re.search(r'^### `([^`]+)`$', section, flags=re.MULTILINE)
            self.assertIsNotNone(match)
            by_name[match.group(1)] = section
        self.assertEqual(set(by_name), set(json.loads(api.INVENTORY.read_bytes())))
        for name, section in by_name.items():
            self.assertEqual(section.count(api.LOCAL_INSTANCE_NOTE), int(name in sites))
            if name in sites:
                path, start, end = sites[name]
                self.assertIn(f'[Frozen source](../{path}#L{start}-L{end})', section)
        intro = ('Twelve rows are marked **Source-local instance registration**: they are not\n'
                 'globally registered typeclass instances, even if the native header says `theorem`.\n'
                 'Explicit-name visibility is distinct from local typeclass registration.\n')
        baseline = markdown.replace(intro.encode(), b'', 1)
        baseline = baseline.replace((api.LOCAL_INSTANCE_NOTE + '\n\n').encode(), b'')
        self.assertEqual(api.digest(baseline),
                         '0a8d84bc9b3e378876c16c365cfbd714162e9ef99ae68b8f3d24393249744944')

    def test_local_instance_source_drift_refused(self):
        path, start, _ = next(iter(api.LOCAL_INSTANCE_SITES.values()))
        sources = dict(self.sources)
        lines = sources[path].splitlines(keepends=True)
        lines[start - 1] = lines[start - 1].replace(b'local instance', b'theorem', 1)
        sources[path] = b''.join(lines)
        with self.assertRaisesRegex(ValueError, 'source-local instance'):
            api.render(self.records, self.html_root, sources)

    def test_source_only_manifest_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'docs').mkdir()
            (root / 'docs/api-manifest.json').write_bytes(
                (api.ROOT / 'docs/api-manifest.json').read_bytes())
            with patch.object(api, 'ROOT', root):
                self.assertEqual(api.source_binding(self.sources), 'committed-source-hashes')

    def test_wrong_revision_module_name_kind_line_and_path_refused(self):
        self.assertNotEqual(api.SOURCE, '0' * 40)
        first_module = next(name for name in api.MODULES if self.records[name]['declarations'])
        def mutate(key, value):
            records = copy.deepcopy(self.records)
            records[first_module]['declarations'][0]['info'][key] = value
            with self.assertRaises(ValueError):
                api.render(records, self.html_root, self.sources)
        row = self.records[first_module]['declarations'][0]['info']
        for key, value in (('name', 'Wrong'), ('kind', 'axiom'), ('line', True),
                           ('line', 0), ('line', 999999), ('sourceLink', '#'),
                           ('sourceLink', row['sourceLink'].replace(api.SOURCE, '0' * 40)),
                           ('docLink', 'wrong')):
            with self.subTest(key=key, value=value):
                mutate(key, value)

    def test_header_tokens_and_missing_site_refused(self):
        first_module = next(name for name in api.MODULES if self.records[name]['declarations'])
        records = copy.deepcopy(self.records)
        records[first_module]['declarations'].pop()
        with self.assertRaises(ValueError):
            api.render(records, self.html_root, self.sources)
        records = copy.deepcopy(self.records)
        records[first_module]['declarations'][0]['header'] = '<script>unsafe</script>'
        with self.assertRaises(ValueError):
            api.render(records, self.html_root, self.sources)
        records = copy.deepcopy(self.records)
        records[first_module]['declarations'][0]['header'] += '<span>extra token</span>'
        with self.assertRaises(ValueError):
            api.render(records, self.html_root, self.sources)

    def test_missing_native_module_and_modified_source_refused(self):
        records = copy.deepcopy(self.records)
        records.pop(api.MODULES[-1])
        with self.assertRaises(ValueError):
            api.render(records, self.html_root, self.sources)
        sources = dict(self.sources)
        sources[api.MODULE_PATHS[api.MODULES[0]]] = b'one line\n'
        with self.assertRaises(ValueError):
            api.observe(self.records, self.html_root, sources)
        with patch.object(api, 'ROOT', Path(tempfile.mkdtemp())):
            with self.assertRaises((ValueError, FileNotFoundError)):
                api.source_binding(sources)


if __name__ == '__main__':
    unittest.main()
