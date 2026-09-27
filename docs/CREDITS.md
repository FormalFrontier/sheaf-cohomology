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

## Native sheafed-space cones and additive forgetting

`SheafCohomology/ConePullback.lean` retains the native cone-pullback
expressions of Worker B Hive Task
`hive-request-a5c686fef9733b91207a12bdbe674244008553c9` (UID
`f70328b3-10f7-4bbc-a451-4678e9530731`), accepted original incubator
expression `f954278ddb91c98cd814c8494c923ef42fcffb2c`. Its Type/Ab
`Fin 3` and empty-cone client expressions are retained privately in
`SheafCohomologyExamples/ConePullback.lean`.

`SheafCohomology/AbelianForget/SheafedSpace.lean` retains the native
additive-to-Type sheafed-space expressions of Worker A Hive Task
`hive-request-b07c9e71ff00cd01911a5a32362418e37d0e7c7d` (UID
`43d607ff-d0f5-4973-98a2-424b5c9e09db`), accepted original incubator
expression `0a8d9c5283e1f973e59bb23aa1894f374e03d137`. Its actual-arrow,
chain and empty-carrier client expressions are retained privately in
`SheafCohomologyExamples/AbelianForgetSheafedSpace.lean`. These results
build on mathlib's native sheafed-space interfaces and the separately
attributed `PullbackCoherence` and `AbelianForget.Pullback` expressions above.

Worker A Hive Task `hive-request-a9348957aad244ebb6858654af192eb53fbae664`
(UID `38cf99b0-2bd7-420f-864d-07924d7f26ba`) transfers both accepted
expressions, adapts only the local import and private clients, and supplies
this guide and metadata. Its exact contribution and checks are identified
in the ordinary promotion PR and issue record. This attribution does not
assert destination acceptance, publication, private source correspondence,
third-party ownership or source-level coverage.

## Cone-wise additive forgetting

`SheafCohomology/AbelianForget/ConePullback.lean` retains the accepted
original mathematical and proof expressions of Worker B Hive Task
`hive-request-a2fbf59ac6e1d618dc6baa300d551b97d9789398` (UID
`49bde45c-5637-4b6b-9e67-d5139ae02188`), original commit
`7ea63759ddf4dfaecee2ecb01336e181fd2d4f54`. Its corresponding
two-arrow, component and empty-vertex client expressions are retained as
private examples in
`SheafCohomologyExamples/AbelianForgetConePullback.lean`.
Worker A Hive Task `hive-request-62a0fc45132ac8b59317baec3bdca816c4c1f829`
(UID `19773a55-4aec-44bc-b843-6cf22fbb1a0c`) transfers these expressions,
adapts local imports and private client names, and updates public guide and
metadata. The ordinary promotion PR records the destination revision and
its separate checks. This credit records expression and transfer, not a new
copyright claim, original third-party rights, destination acceptance,
official publication, source correspondence or coverage.

## Native projection-mate cocones

`SheafCohomology/ConePullbackCocone.lean` retains the mathematical expressions
of Worker B Hive Task `hive-request-b5d71038ee1c27e92bd1d66f62b21001a79f2069`
(UID `001c2dd6-70cd-4f36-92a3-0bee18fb582a`), original commit
`e32952df2893d49f76b8fe96a63db3defd3a4381`. Worker A Hive Task
`hive-request-314f8ea55794f67df587aaab888cb76a998d3007` (UID
`285a5ea5-e220-4df1-8088-816b66f61521`) transferred these expressions and
the Type/additive/empty-carrier client to destination commit
`9e548ad99e4abf08c757cc382562c0709a584ca9`, adapting only imports, header,
client visibility/names and standalone documentation. The clients remain
private; the conditional `colimit.desc` example is a private definition.
Anchor assembled the unchanged Lean leaves into the aggregate roots and
updated public documentation and metadata. Exact destination assessment,
acceptance and publication are separate revision-specific records; this
credit establishes neither third-party ownership nor source coverage.

## Forgetful native cocones

`SheafCohomology/AbelianForget/ConePullbackCocone.lean` retains the three
public laws and private canonical transport of Worker B Hive Task
`hive-request-411a3aeeefaf41c928ba5dd589f2d14811f0a38e` (UID
`8a86b77b-9e0d-48a9-9bda-4d79884fb698`), original expression revision
`3af55bc102c0c81f20271560877d11d786e7ca43`. Worker B Hive Task
`hive-request-fadb8a219b9546f83011af5ec4651e9475d1c1de` (UID
`a79502b5-a697-474a-b3f5-1e42c062fe22`) transferred the production module,
private import-only clients and standalone guide at
`953ab20b8d960e4955962fa870b56d6f5a809226`. Only two production import
paths changed; client mathematical statements and proofs were retained with
destination imports, namespace and private visibility. Anchor added aggregate
registration and updated navigation, credit and lifecycle wording without
changing either Lean leaf. These expression credits do not assert third-party
ownership, destination acceptance, publication, endpoint invertibility or
source coverage; the guide states the exact colimit hypotheses and boundaries.

## Varying-base native diagram pushforward

`SheafCohomology/DiagramPushforward.lean` retains the mathematical
expressions of Worker B Hive Task
`hive-request-3628aceedd705e9f2a33087597c31b7244ce8eae` (UID
`5d89eac6-5b60-41a0-bb24-b0c348237cd7`), original revision
`6c81996064d5679c45aac8864c8269a4e6795383`. Worker A Hive Task
`hive-request-2be4e9b76c87d5c099ccb8d23c1ed738e7063fdc` (UID
`47ed4e53-94f9-4a23-b8e6-db812145fea9`) transferred the producer,
private import-only clients and standalone guide at
`3cd4f7a396193bca86a97b50610986427bc01dba`. Only the two producer
import paths changed; client statements and proofs retain their expressions
with destination imports, namespace and private visibility. Anchor added
aggregate registration and documentation/metadata navigation without changing
either Lean leaf. This origin record does not itself approve the destination,
clear third-party rights, establish source correspondence or publish a release.

## Coefficient forgetting for varying-base direct images

`SheafCohomology/AbelianForget/DiagramPushforward.lean` retains the mathematical
expressions of Worker A Hive Task
`hive-request-620e7673c746798330d114e0e2debbc4a80a2381` (UID
`41fde94b-1957-44b7-9437-430fe5cfd02b`), original revision
`d30bbc667d43143d8c4ecda7c4e8ba3ca3125508`. Worker A Hive Task
`hive-request-0ad06f8848e144e0c34ccd44ac71e2da46c56d58` (UID
`520ced02-de5d-483f-b69f-e8bfb284babe`) transferred the producer,
private import-only clients and standalone guide at
`df460b093e5c846314f97cfac36b3a0fb3f5f930`. Only three producer import
paths changed; client expressions retain their mathematical content with
destination imports, namespace and private visibility. Anchor registered
the unchanged Lean leaves in the aggregate roots and updated navigation,
lifecycle wording and metadata. These expression credits do not themselves
establish third-party rights, destination acceptance, publication or source
coverage; each requires its applicable evidence and decision.

## Native cone reconstruction from pullback cocones

`SheafCohomology/ConeOfPullbackCocone.lean` retains the mathematical
expressions of Worker B Hive Task
`hive-request-fd5f3464b7f33c612645847f878bb0e35e79de1e` (UID
`817007ac-5825-4473-b0be-d3d40a32a445`), original revision
`b8b80ce57222cdbb98c9d17dfca875ea35518a56`. Worker A Hive Task
`hive-request-cbf45ce45ac31f854408fc48bfb3ee338b851bd1` (UID
`8f66d5aa-4564-4c73-92b9-76eb5c62e516`) transferred the producer,
private import-only clients and standalone guide at
`b7746c1bfd3f1426737b40250cc6b8bf95011b3c`. Only the producer import
path changed; client expressions retain their mathematical content with
destination imports, namespace and private visibility. The guide records
original and destination independent reviewer executions. Anchor registered
the unchanged Lean leaves in the aggregate roots and updated navigation,
lifecycle wording and metadata. These expression credits do not themselves
establish third-party rights, final assembly acceptance, publication or source
coverage.
