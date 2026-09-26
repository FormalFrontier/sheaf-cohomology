#!/usr/bin/env python3
"""Render this fixed library's complete native doc-gen4 display inventory.

This adapter checks provenance and presentation, not kernel proofs or the
independent semantic correctness of the displayed mathematical statements.
"""

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess

SOURCE = "a9f1a38787d33205c469ff89710563fffb4974fd"
TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
LEAVES = (
    "AcyclicResolution", "ColimitPostApp", "ColimitTransport",
    "CompactOpenSections", "DegreeZero", "FilteredColimitFunctorH",
    "FlasqueAcyclicResolution", "FlasqueAcyclicSections", "FlasqueResolution",
    "HigherDirectImageFilteredColimit", "HigherDirectImageFilteredColimitPositive",
    "InjectiveResolutionNaturality", "LocalCohomology",
    "LocalCohomologyFilteredColimit", "OpenBaseChange", "OpenCohomology",
    "OpenCohomologyPushforwardResolution", "OpenCohomologyRightDerived",
    "PullbackCoherence", "QuasiFlasque", "QuasiFlasqueAcyclicity",
    "QuasiFlasqueExactness", "SheafificationBasis", "SpectralPreimage",
)
MODULE_PATHS = {
    **{f"SheafCohomology.{leaf}": f"SheafCohomology/{leaf}.lean" for leaf in LEAVES},
    "SheafCohomology": "SheafCohomology.lean",
    "SheafCohomologyExamples": "SheafCohomologyExamples.lean",
}
MODULES = tuple(MODULE_PATHS)
INPUTS = tuple(MODULE_PATHS.values()) + (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json")
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
INVENTORY = HERE / "api_inventory.json"
GITHUB = "https://github.com/FormalFrontier/sheaf-cohomology/blob/"
SITE_CLASSES = {"constructor", "structure_field", "structure_ext_ctor",
                "structure_fields"}
VOID_TAGS = {"area", "base", "br", "col", "embed", "hr", "img", "input",
             "link", "meta", "param", "source", "track", "wbr"}
LOCAL_INSTANCE_SITES = {
    "TopCat.Sheaf.filteredFlasqueResolution_sections_additive":
        ("SheafCohomology/FilteredColimitFunctorH.lean", 623, 629),
    "TopCat.Sheaf.instDecidableMemCarrierOpens_sheafCohomology_1":
        ("SheafCohomology/FlasqueResolution.lean", 38, 38),
    "TopCat.Sheaf.RightDerivedPushforward.evaluation_preservesZero_suffix":
        ("SheafCohomology/OpenCohomologyPushforwardResolution.lean", 1125, 1128),
    "TopCat.Sheaf.RightDerivedPushforward.sheafForget_additive_suffix":
        ("SheafCohomology/OpenCohomologyPushforwardResolution.lean", 1121, 1123),
    "TopCat.Sheaf.RightDerivedPushforward.instAdditiveSheafOpensCarrierGrothendieckTopologyAddCommGrpCatOverOverRestrictToOver":
        ("SheafCohomology/OpenCohomologyPushforwardResolution.lean", 379, 380),
    "TopCat.Sheaf.RightDerivedPushforward.instPreservesInjectiveObjectsSheafOpensCarrierGrothendieckTopologyAddCommGrpCatOverOverRestrictToOver":
        ("SheafCohomology/OpenCohomologyPushforwardResolution.lean", 374, 377),
    "TopCat.Sheaf.RightDerivedPushforward.pushforwardSections_preservesZero":
        ("SheafCohomology/OpenCohomologyPushforwardResolution.lean", 68, 73),
    "TopCat.Sheaf.RightDerivedPushforward.evaluation_preservesZero":
        ("SheafCohomology/OpenCohomologyPushforwardResolution.lean", 63, 66),
    "TopCat.Sheaf.RightDerivedPushforward.sheafForget_additive":
        ("SheafCohomology/OpenCohomologyPushforwardResolution.lean", 59, 61),
    "TopCat.Sheaf.RightDerivedPushforward.presheafToSheaf_preservesHomology_sheafification":
        ("SheafCohomology/OpenCohomologyRightDerived.lean", 39, 43),
    "TopCat.Sheaf.RightDerivedPushforward.presheafToSheaf_preservesZero_sheafification":
        ("SheafCohomology/OpenCohomologyRightDerived.lean", 31, 37),
    "TopCat.Sheaf.instDecidableMemCarrierOpens_sheafCohomology":
        ("SheafCohomology/QuasiFlasqueAcyclicity.lean", 50, 50),
}
LOCAL_INSTANCE_NOTE = (
    "**Source-local instance registration.** This `local instance` is not a globally "
    "registered typeclass instance. This note does not assert explicit-name access."
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def clean(text):
    return " ".join(text.split())


class Header(HTMLParser):
    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.names = []
        self.kinds = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected native header tag")
        require(not any(key.startswith("on") for key, _ in attrs),
                "active native header attribute")
        classes = set(dict(attrs).get("class", "").split())
        if tag == "div" and "decl_type" in classes:
            self.text.append(" ")
        self.stack.append((tag, classes))

    def handle_endtag(self, tag):
        require(self.stack and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(self.stack or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)

    def handle_comment(self, _):
        raise ValueError("native header comment")

    def handle_decl(self, _):
        raise ValueError("native header declaration")

    def rendered(self):
        return clean("".join(self.text))


class SiteParser(HTMLParser):
    """Extract the display sites missing from doc-gen4's top-level JSON rows."""

    def __init__(self, raw):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.declarations = set()
        self.sites = []
        self.active = []
        self.feed(raw.decode("utf-8"))
        self.close()
        require(not self.stack and not self.active, "unclosed native HTML")

    def handle_starttag(self, tag, attrs):
        attributes = dict(attrs)
        classes = set(attributes.get("class", "").split())
        name = attributes.get("id")
        if tag == "div" and "decl" in classes and name:
            require(name not in self.declarations, "duplicate HTML declaration site")
            self.declarations.add(name)
        if tag in {"li", "ul"} and classes.intersection(SITE_CLASSES) and name:
            parent = next((item[2] for item in reversed(self.stack) if item[2]), None)
            require(parent in self.declarations,
                    "nested native site without a declaration parent")
            self.active.append(dict(name=name, kind=sorted(classes.intersection(SITE_CLASSES))[0],
                                    parent=parent, tokens=[], depth=len(self.stack)))
        if tag not in VOID_TAGS:
            self.stack.append((tag, classes, name if tag == "div" and "decl" in classes else None))

    def handle_endtag(self, tag):
        if tag in VOID_TAGS:
            return
        require(self.stack and self.stack[-1][0] == tag,
                "unbalanced native HTML: " + tag + " after " + str(self.stack[-3:]))
        self.stack.pop()
        if self.active and len(self.stack) == self.active[-1]["depth"]:
            site = self.active.pop()
            site["signature"] = clean("".join(site.pop("tokens")))
            require(site["signature"] or site["kind"] == "structure_fields",
                    "empty nested native signature")
            self.sites.append(site)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID_TAGS:
            self.handle_endtag(tag)

    def handle_data(self, value):
        if self.active and not any(
            classes.intersection({"structure_field_doc", "inductive_ctor_doc"})
            for _, classes, _ in self.stack
        ):
            for site in self.active:
                site["tokens"].append(value)


def native_range(info, module, sources):
    path = MODULE_PATHS[module]
    require(type(info.get("line")) is int, "native line not an integer")
    url = GITHUB + SOURCE + "/" + path
    match = re.fullmatch(re.escape(url) + r"#L([1-9][0-9]*)-L([1-9][0-9]*)",
                         info.get("sourceLink", ""))
    require(match is not None, "wrong immutable native source URI/path/range")
    start, end = map(int, match.groups())
    require(start == info["line"] and start <= end <= len(sources[path].splitlines()),
            "invalid native source range")
    return path, start, end


def source_binding(sources):
    require(set(sources) == set(INPUTS), "source/pin inventory differs")
    if not (ROOT / ".git").exists():
        result = "missing"
    else:
        probe = subprocess.run(["git", "--no-replace-objects", "cat-file", "--batch-check"],
                               input=(SOURCE + "\n").encode(), cwd=ROOT, capture_output=True)
        require(probe.returncode == 0, "cannot inspect Git source object")
        result = probe.stdout.decode().strip()
    if result != SOURCE + " missing" and result != "missing":
        require(re.fullmatch(re.escape(SOURCE) + r" commit [0-9]+", result) is not None,
                "source revision is not a Git commit")
        for path, raw in sources.items():
            reference = subprocess.check_output(
                ["git", "--no-replace-objects", "show", SOURCE + ":" + path], cwd=ROOT)
            require(raw == reference, "source/pin drift from frozen revision: " + path)
        return "git-object"
    manifest = json.loads((ROOT / "docs/api-manifest.json").read_bytes())
    require(type(manifest.get("format")) is int and manifest["format"] == 1 and
            manifest.get("docgen_revision") == TOOL and
            manifest.get("modules") == list(MODULES) and
            manifest.get("module_paths") == MODULE_PATHS and
            manifest.get("source_revision") == SOURCE and
            manifest.get("inputs") == {p: digest(raw) for p, raw in sorted(sources.items())},
            "source-only release source hashes differ")
    return "committed-source-hashes"


def load_native(directory):
    require(set(path.name for path in directory.glob("declaration-data-*.bmp")) ==
            {"declaration-data-" + module + ".bmp" for module in MODULES},
            "native module file inventory differs")
    return {module: json.loads((directory / ("declaration-data-" + module + ".bmp")).read_bytes())
            for module in MODULES}


def observe(records, html_root, sources):
    """Build a candidate inventory; compare it to frozen reviewed input in render."""
    require(set(records) == set(MODULES), "native module inventory differs")
    observed = {}
    pages = {}
    for module in MODULES:
        record = records[module]
        require(record["name"] == module, "native module name differs")
        path = MODULE_PATHS[module]
        html_path = html_root / (module.replace(".", "/") + ".html")
        page = html_path.read_bytes()
        pages[module] = digest(page)
        parser = SiteParser(page)
        native_names = set()
        for row in record["declarations"]:
            info = row["info"]
            name, kind = info["name"], info["kind"]
            require(isinstance(name, str) and isinstance(kind, str),
                    "native name/kind malformed")
            require(name not in observed and name not in native_names,
                    "duplicate native declaration")
            native_names.add(name)
            native_range(info, module, sources)
            require(info["docLink"] == "./" + module.replace(".", "/") + ".html#" + name,
                    "native declaration self link differs")
            header = Header(row["header"])
            display = header.rendered()
            require("".join(header.names) == name and "".join(header.kinds),
                    "native header name or kind differs")
            require("```" not in display, "unsupported native header fence")
            observed[name] = dict(module=module, kind=kind,
                                  display_kind="".join(header.kinds),
                                  header_sha256=digest(display.encode()),
                                  doc_sha256=digest(info["doc"].encode()))
        child_names = set()
        for site in parser.sites:
            name = site["name"]
            require(name not in child_names and name in observed and
                    observed[name]["module"] == module,
                    "duplicate native nested display site")
            require(site["parent"] in native_names, "missing native site parent")
            child_names.add(name)
            observed[name].update(native_html_parent=site["parent"],
                                  native_html_kind=site["kind"],
                                  native_html_sha256=digest(site["signature"].encode()))
        require(parser.declarations.isdisjoint(child_names) and
                parser.declarations | child_names == native_names,
                "native HTML/JSON complete site inventory differs: " + module)
        require(bool(record["declarations"]) or not parser.sites,
                "empty module has nested sites")
    return observed, pages


def local_instance_sites(records, sources):
    found = {}
    for module in MODULES:
        for row in records[module]["declarations"]:
            path, start, end = native_range(row["info"], module, sources)
            source_line = sources[path].splitlines()[start - 1].strip()
            if source_line.startswith((b"local instance ", b"noncomputable local instance ")):
                found[row["info"]["name"]] = (path, start, end)
    require(found == LOCAL_INSTANCE_SITES,
            "source-local instance names or source spans differ")
    return found


def validate_markdown(markdown, sources, anchors):
    text = markdown.decode()
    ids = re.findall(r'<a id="(api-[0-9a-f]{16})"></a>', text)
    require(len(ids) == len(anchors) and set(ids) == anchors,
            "generated Markdown anchors differ from declaration sites")
    within_code = False
    for line in text.splitlines():
        if line.startswith("```"):
            within_code = not within_code
            continue
        if within_code:
            continue
        for match in re.finditer(r'\]\(([^)\s]+)\)', line):
            target = match.group(1)
            if re.match(r"https?://", target):
                continue
            require(not target.startswith("/") and not target.startswith("file:"),
                    "absolute generated Markdown local link")
            path, _, fragment = target.partition("#")
            if path == "API.md" or not path:
                require(fragment in anchors, "missing generated local API anchor")
            elif path.startswith("../") and path[3:] in sources:
                require(re.fullmatch(r"L[1-9][0-9]*-L[1-9][0-9]*", fragment) is not None,
                        "invalid source-line Markdown anchor")
                start, end = map(int, re.findall(r"[1-9][0-9]*", fragment))
                require(0 < start <= end <= len(sources[path[3:]].splitlines()),
                        "out-of-bounds source Markdown anchor")
            else:
                require(path in {"Guide.md", "README.md", "CREDITS.md",
                                 "api-manifest.json"} and not fragment,
                        "unresolved generated local Markdown link")
    require(not within_code, "unbalanced generated Markdown code fences")


def render(records, html_root, sources):
    observed, pages = observe(records, html_root, sources)
    expected = json.loads(INVENTORY.read_bytes())
    require(observed == expected, "native site/name/module/kind/signature/doc inventory differs")
    local_sites = local_instance_sites(records, sources)
    lines = ["# Native-generated sheaf-cohomology API", "",
             "Lake development package version `0.1.0`; analyzed source: `" + SOURCE +
             "`; native doc-gen4: `" + TOOL + "`.",
             "These are native **display signatures**, not complete elaboration-ready declarations",
             "or a proof/axiom census. Namespace resolution, inferred types and universes can be",
             "suppressed by native pretty-printing; follow each frozen source link for the exact",
             "binders and proof. Private helpers/examples need a separate complete proof audit.",
             "Twelve rows are marked **Source-local instance registration**: they are not",
             "globally registered typeclass instances, even if the native header says `theorem`.",
             "Explicit-name visibility is distinct from local typeclass registration.",
             "[Module guide](Guide.md) · [Generation contract](README.md) ·",
             "[Credits](CREDITS.md) · [Input manifest](api-manifest.json).", ""]
    anchor_ids = set()
    for module in MODULES:
        rows = records[module]["declarations"]
        scope = "private downstream examples" if module.endswith("Examples") else (
            "aggregate re-export" if module == "SheafCohomology" else "subject module")
        lines += ["## `" + module + "`", "", "Scope: " + scope + ".", ""]
        if not rows:
            lines += ["No native public declaration display sites: this module provides " +
                      ("private checked root-import examples." if module.endswith("Examples") else
                       "public imports and module documentation only."), ""]
        page = html_root / (module.replace(".", "/") + ".html")
        nested = {site["name"]: site for site in SiteParser(page.read_bytes()).sites}
        for row in rows:
            info = row["info"]
            path, start, end = native_range(info, module, sources)
            name = info["name"]
            anchor = "api-" + digest(name.encode())[:16]
            require(anchor not in anchor_ids, "duplicate Markdown anchor")
            anchor_ids.add(anchor)
            lines += [f'<a id="{anchor}"></a>', "", "### `" + name + "`", "",
                      "```lean", Header(row["header"]).rendered(), "```", ""]
            if name in local_sites:
                lines += [LOCAL_INSTANCE_NOTE, ""]
            if info["doc"].strip():
                lines += ["**Native source docstring:**", "", info["doc"].strip(), ""]
            else:
                lines += ["**No native source docstring.** See the source and module guide.", ""]
            if name in nested:
                site = nested[name]
                parent_anchor = "api-" + digest(site["parent"].encode())[:16]
                lines += ["**Native nested " + site["kind"] + " display site** of [`" +
                          site["parent"] + "`](#" + parent_anchor + ").", "",
                          "Native HTML text: `" +
                          site["signature"].replace("`", "\\`") + "`", ""]
            lines += ["[Frozen source](../" + path + "#L" + str(start) +
                      "-L" + str(end) + ") · native range starts at " + str(start) + ".", ""]
    markdown = "\n".join(lines).encode()
    require(len(anchor_ids) == sum(len(r["declarations"]) for r in records.values()),
            "Markdown anchor inventory incomplete")
    validate_markdown(markdown, sources, anchor_ids)
    require(b'version = "0.1.0"' in sources["lakefile.toml"],
            "Lake package version differs")
    nested_count = sum("native_html_parent" in site for site in expected.values())
    manifest = dict(format=1, generator="scripts/generate_api.py", source_revision=SOURCE,
                    lake_package_version="0.1.0",
                    docgen_revision=TOOL, modules=list(MODULES), module_paths=MODULE_PATHS,
                    display_sites=len(expected),
                    top_level_sites=len(anchor_ids) - nested_count, nested_sites=nested_count,
                    inputs={p: digest(raw) for p, raw in sorted(sources.items())},
                    documentation_inputs={p: digest((ROOT / p).read_bytes()) for p in
                                          ("scripts/generate_api.py", "scripts/api_inventory.json")},
                    native_record_sha256={module: digest(json.dumps(records[module], sort_keys=True).encode())
                                          for module in MODULES}, native_html_sha256=pages,
                    api_sha256=digest(markdown), proof_certification=False,
                    release_acceptance=False)
    return markdown, (json.dumps(manifest, sort_keys=True, indent=2) + "\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True,
                        help="fromDb rendered/doc-data directory")
    parser.add_argument("--html-root", type=Path, required=True,
                        help="fromDb rendered HTML root")
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    require(args.source_revision == SOURCE, "wrong immutable analyzed source revision")
    sources = {path: (ROOT / path).read_bytes() for path in INPUTS}
    binding = source_binding(sources)
    records = load_native(args.native_data)
    api, manifest = render(records, args.html_root, sources)
    for name, raw in (("API.md", api), ("api-manifest.json", manifest)):
        target = ROOT / "docs" / name
        if args.check:
            require(target.read_bytes() == raw, "generated file differs: " + name)
        else:
            target.write_bytes(raw)
    print(json.dumps(dict(status="matched" if args.check else "generated",
                          source_binding=binding, modules=len(MODULES),
                          display_sites=len(json.loads(INVENTORY.read_bytes())),
                          api_sha256=digest(api), release_acceptance=False)))


if __name__ == "__main__":
    main()
