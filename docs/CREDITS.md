# Credits, provenance and redistribution boundary

Formal Frontier Agents are the project-wide author credit for original
sheaf-cohomology Lean development and documentation. Repository history and
the issue/ordinary review records attribute work to actual executions; this
collective label neither fabricates individual human contributors nor asserts
copyright ownership. The original project material is distributed under the
official [Apache License 2.0](../LICENSE) text (SHA256
`cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30`).
Formal Frontier's 2026-09-25 standing Apache authorization applies to
verified original project contributions; it does not automatically settle
concrete third-party rights, authenticity of a notice, or an entire public
release history. There is no new human-author or source-author approval claim.

## Original Lean contributors

The following map identifies the **first-added expression** of the original
mathematical modules in this repository's development history. Later promoted
modules have separate origin records below. All listed paths are
under `SheafCohomology/` and end in `.lean`. Anchor authored the original
commits in the first fifteen rows; grouped paths were first added together.
The PR numbers identify their ordinary development review histories, not
first-release clearance. Some modules gained additional results in later
commits, so a first addition does not assign every later line to one author.

| Mathematical module(s) | First-added commit | Development PR |
| --- | --- | --- |
| `CompactOpenSections` | `80c6f1035781ba7849bfa2d88f1978e25a94597b` | #2 |
| `DegreeZero` | `b761738639c5f40079133eafe6eec9e72327ba74` | #4 |
| `QuasiFlasque` | `03bc6cb8c55e6e271db1564ba2303f921193e7a4` | #6 |
| `QuasiFlasqueExactness` | `5e4271cff4eea7ffd28dd701898c7187290d975b` | #8 |
| `QuasiFlasqueAcyclicity` | `d6a8c88901c08812a00df2391e29029f4156dbdb` | #10 |
| `FlasqueResolution` | `b77bb906b0603493cade08def9c54fc361056bab` | #12 |
| `AcyclicResolution` | `1c84221e7b9ecafbb8bc2e4f02434113876df1ad` | #14 |
| `FlasqueAcyclicResolution` | `a94bad1582dccaafd038672866a093915228e2f5` | #16 |
| `FlasqueAcyclicSections` | `585388cf2dd944d015ecd89a684f30047a79beee` | #18 |
| `FilteredColimitFunctorH` | `3f59b05045b9c04ebd9ce9dc1ef9dd09e8872724` | #20 |
| `LocalCohomology` | `eb98f9bfa77e15fdbe28dc5e577e79891a0e9cc3` | #23 |
| `OpenCohomology` | `d37a45dcdaeee00a714be3f82ebc8696545387b2` | #24 |
| `InjectiveResolutionNaturality`, `OpenCohomologyPushforwardResolution`, `OpenCohomologyRightDerived` | `d312d1bd0e326a0afa5d01f1249ab4d95a8e116c` | #25 |
| `PullbackCoherence` | `e22ab8aeb672640f8a0d9b0c5c38ed3204c86aa8` | #27 |
| `ColimitPostApp`, `ColimitTransport`, `HigherDirectImageFilteredColimit`, `HigherDirectImageFilteredColimitPositive`, `LocalCohomologyFilteredColimit`, `SheafificationBasis`, `SpectralPreimage` | `47c42f1fda22327ad2b891cfe122d1629dd900c5` | #29 |
| `OpenBaseChange` (Worker A) | `8dbc0e7bd455e561bd9e0b20860fcc697096b46e` | #33 |

Anchor first added the aggregate `SheafCohomology.lean` with
`CompactOpenSections` at `80c6f1035781ba7849bfa2d88f1978e25a94597b`;
later accepted subject-module additions updated its imports. Anchor's
`QuasiFlasque` later gained the set-valued generalization at
`a9165b2dc424a0542e7cb4ad3c9526ef49f60bee` (PR #31).
The `OpenBaseChange` author is Worker A Hive Task
`hive-request-89f88273be11e82cd4925df7e75bc2866bda40dc` (UID
`e946780e-83d8-4eee-85b7-03a72f9c3506`; issue #32 comment 32050,
PR #33 review 2567). The module-system/public-import readiness work on
the existing 25 Lean paths and the first expression of the named **private**
`SheafCohomologyExamples.lean` client are Worker A commit
`c74593442ab9aacc0b900f9c189e78a96c91fb05`, Hive Task
`hive-request-afcf4270369d5826e41fa8de5e8d3ddf01f6f949` (UID
`ce46d245-90e8-456a-8c2c-c8cb14b58f23`; issue #34 comment 40344).
Anchor assembled the separate readiness documentation/metadata successor;
PR #35 review 3006 and owner record #34/40581 accepted only ordinary
development readiness. These Git and review identities establish project
contributions, not underlying human identities or a new whole-proof review.

## Documentation adapter origin

The fixed-library adapter in `scripts/generate_api.py` and its data-only tests
in `scripts/test_generate_api.py` adapt original-project expression and patterns
from Anchor's ideal-completion adapter at
`a6f4d9c9614c20fe05f947902373d60e05504291` and the ADL
(algebraic-direct-limits) native adapter at
`bbdcf43d28dd92312484adba53fe20b5b35a2f75`, especially native
header parsing, fixed-site controls, immutable source URI/range and source/pin
binding, source-only hash reproduction and Markdown rendering. The sheaf
adapter adds its 26-module/556-site inventory, nested HTML site extraction,
and its own checks; it is not a verbatim vendored doc-gen4 implementation or
third-party generated website. The shared original-project adapter work is
covered by the standing Apache authorization. These references identify actual
reuse, not a claim that this documentation Task invented every adapter pattern.

Lean 4, mathlib and the nine resolved manifest packages are declared external
dependencies; their source code, caches and generated dependency websites are
not vendored in this repository. The separate native doc-gen4 tool at commit
`97d4ecdfc8e09e7f511724c25e303d448de6a3db` generates the display records.
This library ships its own Markdown API rendering of those records, not the
tool's generated website, CSS, scripts, fonts or compiled executable. The
signatures and docstrings derive from this library's Lean files, and the
generated reference links back to those files. Tool licensing and the exact
resolved inputs must still be checked when distributing bundled binaries or
third-party material; none is bundled here.

Mathematical background includes native mathlib's category, sheaf, Ext and
derived-functor interfaces and Fujiwara and Kato, *Foundations of Rigid
Geometry I* (arXiv:1308.4734v5). The latter is a reference for mathematical
ideas, not a claim of verbatim theorem correspondence, copied prose or human
endorsement. No book PDF, figure, scan or substantial source excerpt is shipped.
The source-specific correspondence and remaining coverage gaps belong in the
source metadata, not this independent mathematical library.

This documentation assembly is authored by Hive Task
`hive-request-005cc1192de1d317fa08cbb47205c76f49a3dcf2` (UID
`522b1a6f-e533-4c43-8411-2d6438d8a2b8`, request
`6fef9e2a701d3cfa241a8b68d5f60a97`), starting from accepted development
main `a9f1a38787d33205c469ff89710563fffb4974fd`. The bounded
documentation/provenance successor is Worker B Hive Task
`hive-request-6b499b4884d3f37633f4b86b64ccccaa6a5468da` (UID
`f259b7c1-2916-4f77-8d61-626d6fd28821`), with sole parent
`0462cd30a2047222e76996540f7ed719cc8b16ec`. Independent redistribution,
provenance and semantic assessment of the complete artifact and its public
history is separate from this credit record; this file alone is not acceptance.

## Abelian-sheaf forgetful comparison origin

The three `SheafCohomology/AbelianForget/` modules and two private example
clients retain actual originating expressions, not only collective credit.
The canonical pullback mate and coherence construction originated with Worker A
Hive Task `hive-request-69989e5f0656c9c3a172d5885b8421f7b778e824` (UID
`b2938834-7079-41f8-89b9-48cd2ff03e56`, original source contribution
`7edfb11d6c73afa3ca750104de5e874a5923b256`, original PR #264).
The filtered-colimit development originated with Worker B Hive Task
`hive-request-2f1e332761386974784954a2af9a56f1d3a63952` (UID
`196336cd-b105-42e7-a64f-165eff075740`, original source contribution
`ca2a03cd95000ae48c36bf2b592427633ff6560f`). The expressions were
adapted into the incubator by Worker B Hive Task
`hive-request-75271e0d032ad91de7edf45b55be683b44fbda68` (UID
`80510ac9-3072-40c1-8775-7b674b6b0bd8`, adaptation
`66fd36bade0aeb5a8be8a89a82122603483b35c1`, accepted incubator main
`2dd64258efb1c625d42a21f8c0cfa80dd60c54cf`).
The bounded destination import/client and documentation transfer is Worker B
Hive Task `hive-request-0a302a17bb4dc6a1c08d2b391bafc71386213178`
(UID `0aa564c2-3d8b-41cf-92cb-bdb369a229ce`); its exact contribution commit
is recorded in the ordinary PR and issue handoff. None of the source-specific
correspondence, research or review logs is shipped with this library. The
standing original-project Apache authorization concerns verified original
contributions; it neither assigns ownership nor certifies third-party rights.

## Generic square-transition origin

`SheafCohomology/SquareTransition.lean` preserves the accepted coefficient-generic
incubator proof expressions byte-for-byte. Anchor supplied the original
source-local Type-valued expressions at `474d7f975dcc8560f4182a83f7b6bbe32cbf6762`
and `6daac54906b30cd4be04aff2ab15b1718eaed9ed`. Worker A Hive Task
`hive-request-416add33a92643818723dcd89e0c302ac3fc98ee` (UID
`17ae3110-d3f0-4dbc-b21e-0824cce5b1e9`) generalized those expressions;
its original contribution was `5747eff2fdefe3dd4231fb73b6925e67f7393b69`,
assembled by Anchor at accepted incubator revision
`a2c6e8b61dcb5984c47e2af9e9c5203dffd4a88a`.
The destination transfer and eleven private clients are Worker A Hive Task
`hive-request-7446c1ce80d48017bc2bb5c6319ed8a16b6f463e` (UID
`727fdb1b-44a5-425e-87ed-10e2fb326d8a`), contribution
`4c222183f2bd7790f78a92e8b8699938a3cc978b`. Anchor supplied the aggregate
exports and documentation assembly. These are internal expression credits,
not source correspondence or a claim that private development objects are
published on GitHub. Research records and raw check transcripts are not shipped.

## Forgetful square-transition origin

The four public bridge expressions in
`SheafCohomology/AbelianForget/SquareTransition.lean` and the
`SquareTransition.adjoint_eq_homEquiv` helper originate in the accepted
incubator revision `d6135ec9832e5ff93d267fb2c1eaeb0aa2ea1eed` (ordinary
incubator PR #22). Their original Worker A author was Hive Task
`hive-request-86c6c966eb9b2f38ea3301684200792d9b071449` (UID
`95cfe360-9cce-4918-b8c4-d71cf3b3cfca`); its preceding expression commits
include `617ee2f` and `3c8e049`. The source's five public-import client
expressions are retained as private destination examples. Worker A Hive Task
`hive-request-ca9bade41d94586a071a4b71d29e1638d361c631` (UID
`4521520d-7491-4854-b7c3-57437bc9ca4b`) transfers these expressions,
adapts imports and presentation, and records the destination proof checks.
The ordinary promotion PR identifies the exact destination revision. This
expression history is not a claim of destination acceptance, release, source
correspondence, third-party ownership or human endorsement.
