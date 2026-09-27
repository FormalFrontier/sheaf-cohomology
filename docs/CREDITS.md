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

## Native sheafed-space limit criterion

`SheafCohomology/ConePullbackLimit.lean` and the public
`pullbackCompInv_assoc` wrapper in `ConePullback.lean` retain the mathematical
expressions of Worker A Hive Task
`hive-request-1ffb62254e0abad263d5c38689c61350e1754c8d` (UID
`814f8840-45a3-4bc4-80b7-ad647577a977`), original revision
`91beca03735ce5c91e9378bc79c5998f21d95eb9`. The original independent
review is Worker B Task
`hive-request-316714e9591cab45a00dfeac2201a1538e894773` (UID
`c3c034f4-40d1-4d3e-9dad-d81fa269ef4d`), revision
`4af64d66834fa2edf380a83e9685f5669911f6f6`.
Worker A Hive Task `hive-request-591c0dc5ae5baa51942d167d38d6997286570e85`
(UID `07e0359e-2ac4-46f4-ab6d-abda07d5d014`) transferred the producer,
private clients, guide and unchanged wrapper at
`02227d05e511c60af206413754591e559aed6cc5`. Only the producer import/header
and client imports/namespace/visibility were adapted. The predecessor cone,
cocone and native-reconstruction expressions retain their separate credits
above. Anchor added aggregate registration and updated navigation, lifecycle
wording and metadata without changing the three Lean leaf blobs. Original
review does not certify this destination or its later assembly; independent
destination/release assessment, maintainer acceptance and verified publication
are separate. These credits establish neither third-party ownership nor
source correspondence or coverage.

## Actual native sheafed-space limit construction

`SheafCohomology/LimitConstruction.lean` retains the mathematical expressions
of Worker A Hive Task
`hive-request-700e4f0e3debb32b4538a1158e70ca099e66c254` (UID
`02943c65-933d-4b1e-974b-decbd5d5f153`), original accepted revision
`f30d2befa872ce170736d97a72444790847365e5`. The original independent
mathematical reviewer is Worker B Task
`hive-request-f56d422e9bac1b8c13465b1dc849cc5f891a493a` (UID
`2eedc5aa-54f0-479d-a611-70a1049ec996`), report revision
`c8a4369a1b025cd658807ebdaaa21084e6e5432c`. Worker A Hive Task
`hive-request-6dd6bbaa5fa6642467da4af8d0dff8a12786d1c4` (UID
`b6d76148-1649-49aa-943e-731466986081`) transferred the producer, private
import-only clients and standalone guide at
`b6d4464d6b38e0faa54d263ba653d8ebac0e69b2`. Only the producer's predecessor
import and the client imports, namespace and visibility were adapted.
Anchor registered the unchanged Lean leaves and updated navigation, guide
lifecycle and metadata. The construction reuses the separately credited
cone-reconstruction and limit-criterion expressions and mathlib's site-sheaf
colimit instance. These credits do not certify destination acceptance,
publication, third-party ownership or source coverage.

## Native-to-space limit preservation

`SheafCohomology/LimitPreservation.lean` and its private clients retain the
mathematical expressions of Worker B Hive Task
`hive-request-502206a7e28d7384c6a1ab57a9acf7a38c6a9eb4` (UID
`5a505fe4-97ca-426f-8b06-9149e72762b3`), original accepted leaf
`458297b9feef7fe8b838aa91db2944f53d23293a`. The original independent
reviewer is Worker A Task
`hive-request-7996da543adddee2f16c056f6551863372a81898` (UID
`4f167d3a-f251-4072-b17f-edabe055d33b`), report revision
`e7029896a2f9b3c22f0de6e118d6e6eb989f33a2`. Worker A Hive Task
`hive-request-6d9e8f29fa46918f8089bb987efa7985c6f27b00` (UID
`6a32dd01-a3e7-451f-a859-bd1347902e71`) transferred these expressions
at destination `8d587a97c5de06a3327d0720e237391e161610da`, changing
only one producer import and the client import and namespace. Anchor added
aggregate registration, navigation, lifecycle wording and metadata while
preserving both Lean leaf blobs. The prerequisite construction, criterion,
cone reconstruction and mathlib preservation API retain their separate credit.
Original review and these expression credits do not certify destination or
aggregate acceptance, publication, third-party ownership or source coverage.

## Cofiltered limits after forgetting additive coefficients

`SheafCohomology/AbelianForget/LimitPreservation.lean` and its private clients
retain the mathematical expressions of Worker B Hive Task
`hive-request-13fb7168e78b10adc0a739488a5b88a5bad2cd58` (UID
`9a8d7368-37db-444c-b740-2b889ce82678`), original accepted leaf
`bca0b7e2157ff42e7fee82a844a24ed64bd81957`. The original independent
reviewer is Worker A Task
`hive-request-e191e9001fd91ccc94ac716347cfe494151b243a` (UID
`e456f556-7b89-45ca-a633-7c5641bb1484`), report revision
`012dbb7d96b8692316e94ba000e5d85108222cf2`. A distinct Worker A Task
`hive-request-e5601633e037e2e255c65a2ce615260dafca7b25` (UID
`08e5a83e-3ade-46bf-8ef3-64545240ab1c`) transferred the producer, private
clients and guide at `0e2502047fb6f4ae1fea71132cbe25d74aac2077`, changing
only three producer imports, one client import and its namespace, and adding
explicit comment-only Apache/original-author notices to both Lean files.
The fresh independent destination-leaf reviewer is Worker B Task
`hive-request-50aefd26f24f869e97ac447c866866dfd7b401e5` (UID
`eec8c8c6-7bf7-415d-a65a-0158821d942d`), report revision
`bf34ba8739f38b4196c7b6bc85ed778560efce2a`; its scope excludes this registration
and the inherited graph and does not constitute a native PR approval.
Anchor registered the unchanged Lean leaves and updated navigation, lifecycle
wording and metadata. Filtered sheaf-colimit preservation, native cocone
transport, the actual-limit construction and their mathlib inputs retain
their separate credits. Original leaf acceptance does not certify this
destination or registered graph, clear third-party rights or publish a release.

## Fixed-base converse for native sheafed-space limits

`SheafCohomology/ConePullbackLimitConverse.lean` and its private clients retain
the mathematical expressions of Worker B Hive Task
`hive-request-5c0d008960ac42fcbe67c583368b2de1262bc7a6` (UID
`1e7508ec-7d20-4c36-8393-f3d49db2f034`), original accepted leaf
`04bbd0de0261b5a8700a37ac21709fa247c7ffe5`. The original independent
reviewer is Worker A Task
`hive-request-be8be110d4df284a21383c998c3f79eaa0e9d665` (UID
`59ba953e-e1f3-423e-80c2-36cbce0bb980`), report revision
`35a5466ea1b9e68b0eb50cdf3c5565a209dc2f34`. A distinct Worker A Task
`hive-request-2db87e045f6161e5d842a9fbf578054eceb228a2` (UID
`2d2da29d-c711-4c27-90b8-9f8f0a860f18`) transferred the producer, clients
and standalone guide at `c01a006d2199d6ffd9ef2713731323c29c60c67a`.
Only project imports, client namespace/visibility and expose presentation,
an import-description comment and comment-only SPDX/credit notices changed;
all mathematical statements and proof bodies were preserved. Anchor registered
the unchanged Lean leaves and added navigation, lifecycle wording and metadata.
The original independent review is not approval of this destination or final
graph. Native cone reconstruction, projection mates, pullback coherence and
the forward criterion retain their separate credits. No human endorsement,
third-party rights clearance, publication or source coverage is inferred.

## Native cone-pullback section transport

`SheafCohomology/ConePullbackSections.lean` and its five named public
ordinary-import clients retain the expressions of Worker A Hive Task
`hive-request-56a0f46868a5a666cdc4e1ce2d7423802e462456` (UID
`6168c7bc-d47b-4305-a538-58d1350272d0`), repaired by Worker A Hive Task
`hive-request-6d526071fadec30d7ff2b4abfed7d988d35a78da` (UID
`d4885694-78ac-4ce2-bc13-f81029f15673`) at accepted incubator leaf
`dd4ba173e5dda37074b47a16c4fa7647305149fe`. The repaired leaf's fresh
independent reviewer is Worker B Hive Task
`hive-request-71f983a9268c32fce086bf8f2f49cddf5c6eeb15` (UID
`45597500-b870-4e33-b97f-ca2408f918fb`), report
`f2cab0cb921b5cf81a3db9e99377a13903fbbbb4`. The original superseded
candidate's review objections remain recorded; this is not a waiver of them.

The private `adjoint_comp` proof expression closely adapts Anchor's
`adjointTransition_pullbackTransitionComposite` in
`Research/fk-proposition-3-1-10-pullback-coherence-scratch.lean` at source
revision `e266a5076df34934171cc284ba8f2834e56f8c78`, including its
adjunction-uniqueness comparison, `change` and successive rewriting steps.
It also follows the separately credited `mateComp` proof in this library's
`ConePullback.lean`, published at
`e4c7d681e0913fc1dde266cfcfc37763f1d47785`.
The source/target restriction proofs closely adapt Anchor's
`Research/fk-proposition-3-1-10-adjoint-transition-naturality-scratch.lean`
at that source revision. The old stage-section-transport probe supplies
mathematical motivation, not an imported stage-system implementation.
[The section guide](ConePullbackSections.md) gives the expression-level
distinctions. No source research files or source PDF are shipped or imported.

Worker A Hive Task
`hive-request-8a7211e66bf0303b4ffc778195cdf17b95093b09` (UID
`e1cd2f5b-de9b-4f1a-b4a9-6e7df9d766dd`) transferred these expressions at
`e770f0fa714c83bc735b7ed22f3abeb853fe7cdb`, adapting only producer
namespace, ordinary client import and qualified names, and standalone guide.
Anchor added aggregate registration, truthful example visibility, navigation,
credit and lifecycle metadata without changing either Lean leaf. Source-leaf
acceptance and focused destination checks do not establish final destination
review, combined-graph acceptance, publication, third-party ownership or source
coverage. The destination depends on mathlib, not on an incubator or source
revision; development ancestry is not part of the public release history.

## Native inverse-image local sections

`SheafCohomology/PullbackLocalSections.lean` retains the byte-exact native
implementation of Worker B Hive Task
`hive-request-c862e7aa8f5b10a37f55dbfbfcc07250a83772cd` (UID
`0b29aa2c-31b4-4085-b8ae-dfec0cb71756`), accepted as unregistered incubator
leaf `9cba716e58ac499e102abfadeccd811d1b0c23cf`. Its fresh independent
source/leaf reviewer was Worker A Hive Task
`hive-request-7708ef819d1da79f05079e569149a3a3b5fbcfe5` (UID
`10306134-381d-434b-ab66-8077fb2a93da`), report
`af4468a1593d2c2a75320324352d51b0e4a886b0`. Superseded warning-option
defects are not retrospectively accepted by that corrected-leaf review.

The private `constructed_unit_hom` closely adapts the **proof expression**
(`change`/`simp`/`rfl`) of Anchor's
`sheafPullbackConstruction_unit_app_hom` in
`Research/fk-proposition-3-1-10-stage-section-transport-probe.lean`, source
revision `e266a5076df34934171cc284ba8f2834e56f8c78`, blob
`939e35949d83eb00f63856f702ed93dd9c7fff66`, around line219. This is
expression-level attribution, not merely mathematical motivation. The proof
also reuses mathlib's native adjunction uniqueness, presheaf stalk comparison,
sheafification stalk isomorphism and sheaf separatedness; no alternate
inverse-image model or source-research file is imported.

Worker A Hive Task
`hive-request-6a01a72d5e80988d20b9716dc7419592c896c3a4` (UID
`dcf69e1a-2f1d-43ba-8000-b176eb638e64`) transferred the producer unchanged
at `f62df0bfdd7c93458c29fb8818fa16f72a1459fc`, adapting only the four-client
module's public import and namespace and the standalone guide. This adapter
execution is distinct from the earlier source reviewer. Anchor added aggregate
imports, navigation, lifecycle metadata and this credit without changing either
Lean leaf. [The local-sections guide](PullbackLocalSections.md) states the
precise APIs and boundaries. Source-leaf acceptance and focused destination
checks do not establish final registered-graph review, code acceptance, release,
source coverage or third-party ownership. Original Apache notices are retained.

## Native stage-section equality

`SheafCohomology/NativeStageSectionEquality.lean` and its two public ordinary-
import clients copy the full Lean statements and proof expressions of Worker B
Hive Task `hive-request-83333dedd640d855f159f1c115a70d659ba2c7dc` (UID
`ce8bbfcb-4d1f-4e5f-b043-5ec831bc6bcd`), accepted unregistered incubator leaf
`c7818152bd5ebef3d768de238962bf9fc04fb7fc`. Original fresh independent
review was by Worker A Hive Task
`hive-request-a44553406806c535fda284689c5428b6e55f00ff` (UID
`54ee6779-5591-4608-b802-3906536cc1a7`), full report
`9419e5f00d105a682c613d75ec6f42f724e7aa05`. Original Apache notices remain.

Worker A Hive Task
`hive-request-ff998c4cc73fa7cfcec2d169e68b78c8e14c7e0a` (UID
`d11b0afb-7e2c-44a8-b31c-78fe5a3637f7`) mechanically transferred the full
producer and client expressions, changing only one producer import, one client
import and two client namespace occurrences. The corrected adapter is
`a8d55b29bd54372d8e480bd3b8f9eef9b34ec9d2`, retaining its predecessor
`30586e92446453bb4c53a88f2cb68318fdf6d92b`. Reverse substitutions recover the
original Lean blobs `cbc6ebe0b1de22a941f373c550d92d6d2579259a` and
`e14d0b3ada7690fb1d43f9704d472afc10712203`. Anchor added root registration,
navigation, lifecycle metadata and credit without changing either Lean blob.

Anchor's earlier source-local whole-stage equality probe at source revision
`e266a5076df34934171cc284ba8f2834e56f8c78` supplied mathematical motivation,
not a copied proof expression for the original native implementation. This is
distinct from the full expression-level copying in the destination transfer.
[The stage-equality guide](NativeStageSectionEquality.md) identifies that
probe and the original native proof's local-unit, spectral-cylinder and
naturality ingredients. Their separate contributor credits remain applicable.
Official spectral-stone-duality and its ideal-completion dependency retain
their own notices; neither incubator ancestry nor source research is imported.
Original leaf approval and focused transfer checks do not approve this
registered destination graph, establish release or source coverage, identify
a third-party copyright holder, or imply human endorsement.

## Native whole-stage section lifting

`SheafCohomology/NativeStageSectionLifting.lean` and its two private
ordinary-import clients copy the **full original Lean statements and proof
expressions**, not merely mathematical ideas, of Worker B Hive Task
`hive-request-e5e544a630e9b84215130384682791cdebd0aea0` (UID
`3bb51737-f69e-4698-9538-9f0336c572d9`), accepted unregistered incubator leaf
`055857c06b98686dfc9f33f77f401f1dda2cc150`. Original fresh independent review
was by Worker A Task `hive-request-9639b5e9869b8855e5090d224960c07301b3aa4e`
(UID `7a8d0f31-e6c4-47d6-95e2-ac99a9886260`), report
`3759f8ed0fb4c2c07b330916a7448acad51ee7d5`. Original Apache notices remain.

Worker A Task `hive-request-ed4ccda04a6ba2607731fe00b73853080a0f5761`
(UID `9aa315b6-c463-47b1-a6cb-7cd8989f4f72`) supplied the narrow destination
adapter and guide at `62cfed9272084323871d7ffc0a47284bbf3b1985`. Its only Lean
changes are one producer import, one ordinary-client import and the client
namespace/end. Reverse substitutions recover original blobs
`9b11134348177180ad1855660691d87ac52ffe71` and
`cd56b7c16a5fdb68977b7db20ec0c32506235d63`. Anchor registered these unchanged
Lean leaves and updated navigation, lifecycle and credit; this is distinct
from the original proof implementation and independent review.

Anchor supplied the mathematical motivation and whole-stage descent design.
The [lifting guide](NativeStageSectionLifting.md) records the separate native
local-unit, equality, cone-section transport, finite-cylinder cover and
synchronization/gluing design contributors. Their credits and dependency
notices remain applicable. No incubator ancestry is imported into the public
release history. Original leaf acceptance and focused destination evidence do
not establish acceptance of this combined graph, verified publication,
source coverage, third-party ownership or human endorsement.

## Native stage-section colimit comparison

`SheafCohomology/NativeStageSectionColimit.lean` and its two private
ordinary-import clients copy the **full original statements and proof
expressions** of Worker B Hive Task
`hive-request-bf36c0a2309835a3fdfa6d14f20ebde4191ab672` (UID
`1addeab3-992e-4fed-aa4b-afcea8e2487c`), accepted unregistered incubator leaf
`1bad295cf6a96a5da13105442982a55e17efb5ec`. Original independent review was
by Worker A Task `hive-request-7b1e8ba3ec50fa7889d32b48e6e638db24c101b8`
(UID `a86d4770-966b-43ad-8b5d-ca56f8e44a82`), report
`35292e96298179d531f70abfc23d6d85ca17e9fc`. Original Apache notices and
the separate source evidence `0568c4e2f088f6b44727883bf564b095bf9c54b0`
remain applicable within their recorded scope.

Worker A Task `hive-request-0379bab87d7c2b4512b09a37865419d3586e95c2`
(UID `7d5fd314-be18-4a43-8f5c-f6407812944d`) supplied the narrow destination
adapter and standalone guide at `7dd9de3a3f8f8ab113fb6be8356df44b49e03c0a`.
The only Lean substitutions are one producer import, one ordinary-client
import and the client namespace/end; reversing them recovers original blobs
`f8966a17216572a0316604118c37e41d7348070d` and
`770f312d7b9f5f1cf949fd60d9442399abdc76d8`. Separate destination evidence
is `06e9dbab113c651b06de411a991f09c531aba6ab`.
Anchor registered the unchanged Lean leaves and updated navigation, lifecycle
and credit, separately from the original implementation and independent review.

The [stage-colimit guide](NativeStageSectionColimit.md) preserves the native
equality/lifting and cone-section contributors and distinguishes Anchor's
finite-descent design from copied proof expressions. The destination invokes
those interfaces and mathlib filtered-colimit results, not external source
text. No incubator ancestry enters the public release history. Original leaf
acceptance and focused transfer checks do not establish combined-root
acceptance, verified publication, source coverage, third-party ownership or
human endorsement.

## Chosen native-limit global-section comparison

`SheafCohomology/NativeLimitGlobalSections.lean` and its private ordinary-import
client are copied statement **and proof expressions**, narrowly transferred
from accepted unregistered incubator leaf
`00d551efc598b8252fbc694830523b830bf94a27`. Original author worker-b Task
`hive-request-4c216dbec01d4be3c9179c965656f0054d638fb8` (UID
`b5bc6fa6-d9ab-4cfa-bd79-3ec1cdf7265a`) supplied the implementation;
fresh independent worker-a Task
`hive-request-63bb28dd0ebca9eed6f1f8633171e93fdbe4cf95` (UID
`ef75b120-2781-4310-bec4-25989baec649`) reviewed it in report
`5de42c13795f2b53f09f3aaf3955a74832ebfa06`, followed by Anchor's
incubator #4/comment 53518 leaf acceptance. The original `592629` candidate
and evidence `cad6a92baed502c134939e6dabc7db6135dc1f6d` remain historical;
`00d551` corrects one guide citation, not Lean expressions or earlier nonpasses.

Worker-a adapter Task `hive-request-4a0c71a3b9ce2bd856ab1a6b47ce89a98433112e`
(UID `eb69c4df-f917-40c5-b2c6-b5b1c344080f`) transferred the payloads at
`68d837027efcd3e61dd5ef80ff9a0153f8e178e0`. Reversing one producer import,
one ordinary-client import and its namespace/end recovers the original blobs
`89e1bdca0160dc88665cc6a024bdb24422bebcbc` and
`c4c386299561a77415f1825e55c51e0c38fe86c5`. Separate destination evidence is
`0ce32352e38c75721ee011e132ea513d4c589a69`. Anchor's design
`4c52c039a83ad2579e4978686c5bc2aac818992e` is not compiled proof evidence;
Anchor separately registered the unchanged Lean leaves and updated lifecycle,
navigation, metadata and this credit.

The two compact/prespectral transfer helpers adapt proof expressions from
worker-b Task `hive-request-e5e544a630e9b84215130384682791cdebd0aea0`
(UID `3bb51737-f69e-4698-9538-9f0336c572d9`)'s native lifting implementation;
the quasi-separated helper follows that pattern using a different official
result. The original collector adapts worker-b Task
`hive-request-bf36c0a2309835a3fdfa6d14f20ebde4191ab672` (UID
`1addeab3-992e-4fed-aa4b-afcea8e2487c`)'s predecessor harness,
evidence `0568c4e2f088f6b44727883bf564b095bf9c54b0`.
The [standalone guide](NativeLimitGlobalSections.md) preserves these distinct
contributions and actual projection/factorization semantics. Other published
mathematics is invoked, not copied; no private source text is included.
Original Apache notices remain. Leaf acceptance and focused checks do not
establish combined-root acceptance, release, source coverage, third-party
ownership or human endorsement.

## Native restriction to inverse-image opens

`SheafCohomology/NativeOpenRestriction.lean` copies the full original statements
and proof expressions byte-for-byte from accepted unregistered incubator leaf
`800f8c79310c54ade745f79d947f98830272f357`, by worker-a Hive Task
`hive-request-dae0d04e8618b53de43730479c4033d21488695b`
(UID `38967a21-9f85-493d-b98f-67dd712fb00e`). Its private ordinary-import
client retains the composed-arrow proof, changing only the import and namespace.
Fresh worker-b Task `hive-request-4796946df145f280a3210441cf31ddeb69e8fe93`
(UID `d8645b6d-38a8-48fa-a133-7c2a61a0caea`) approved that exact leaf in
`1ee5876b03792fabfa806df81a2abe55f94679d4`; Anchor separately accepted it
unregistered on September 27, 2026.

Worker-a Task `hive-request-5de3ebfab00e632e44a5c020cb1fd800467bc20f`
(UID `ac4b4dd0-3208-40c0-9352-a602f551452a`) transferred the two Lean leaves
and standalone guide at `b9496a1ded04552f9619acdcda5f6257b5c9ebe1`.
The producer blob remains `bb04377ad3fd03e9da55e91b41a609fe9e8c38f3`;
reversing the client's import and namespace substitutions recovers source blob
`2945bdf9d3dfae37a1d747b14d6ecad4d77aeab6`. Separate focused destination
evidence is `431ca8a1a80ac5b62be0e8c86897faaeabf0ea50`. Anchor's registration
adds roots, navigation, metadata and credit without changing those Lean leaves.

Andrew Yang's Apache-2.0 mathlib open-immersion lift supplies the construction,
factorization and uniqueness; mathlib also supplies native restriction and `Γ`.
The official Apache-2.0 `OpenBaseChange` unit by Formal Frontier Agents supplies
the `preimageMap` expression and inclusion equation. The
[standalone guide](NativeOpenRestriction.md) separates these contributions.
Original Apache notices remain; no private source text or incubator ancestry
is imported into release history. Original leaf acceptance and focused checks
are not combined-root acceptance, publication or source coverage.

## Native limits of principal-tail open cylinders

`SheafCohomology/NativeCylinderLimit.lean` transfers the accepted-unregistered
incubator leaf `bf566ea767083405992cb832df9e914712a9e3cb`, changing only its
parent import. Original cylinder mathematics is by worker-a Hive Task
`hive-request-153a0400bb1a4285602d24cceb51ae9a56b6b3be` (UID
`38e90320-4a49-4738-9620-3881f7b58af5`); separate worker-a Task
`hive-request-d984b1de170e87f4be31d9ce565c90299c51e3b3` (UID
`35dd220a-f8a8-4fae-9d05-4a503f2f4b96`) repaired the headers and provenance.
Fresh worker-b Task `hive-request-1e8c6a88bf42d9183522899d2ed7cbc7bf9d1916`
(UID `1c65573c-8563-4434-8dbf-138514e62c9a`) approved exact bf566ea in
report `85aeeef35c3b3f0f01d56869b448a4f49e05f5b5`, resolving—not waiving—the
earlier `234e1ae9448fd3eec5bd4250260d9331ebfe8f9a` provenance objections.
Anchor separately accepted that leaf unregistered in incubator #4/54011.

The directed-tail inclusion, directedness, finality and opposite-initiality
expressions adapt worker-b Task
`hive-request-065ffb46d5b6d2b9ada197a66b9c1b783b57e00f` (UID
`4720124c-2740-40ba-947d-5be3c681f64e`), original source commit
`e827107b7a1c6a8cf187189bda816f08931e269a`, retained at
`e266a5076df34934171cc284ba8f2834e56f8c78` in
`FormalFrontier/source-fujiwara-kato-rigid-geometry-i`,
`Research/fk-corollary-3-1-12-open-tail-restriction-scratch.lean:27–49`.
The native restriction predecessor is by worker-a Task
`hive-request-dae0d04e8618b53de43730479c4033d21488695b` (UID
`38967a21-9f85-493d-b98f-67dd712fb00e`); its separate credit above remains.
Andrew Yang's Apache-2.0 mathlib open-immersion lift and native restriction
infrastructure, plus mathlib's categorical finality/initiality results, are reused.

Worker-a Task `hive-request-403dd29c9f3677cefb56ce16b370b5872f9bc61a`
(UID `2d67f405-088f-4811-8d5a-6dce4586b1a3`) transferred the two Lean leaves
and standalone guide at `194e6310aad7205ff53e33cc73e9ba16b5f9398d`.
Reversing the producer import and client import/namespace substitutions recovers
donor blobs `ba08ef145b4831c283171dafee4984ae66648d3a` and
`cd03cbe3c9597caa5f394a68a4b08b377b65bfe1`. Separate destination evidence is
`b5ac3f80af7ae5bb02d38fb8189bfcea1046469c`; donor-only evidence
`a4d4bfe750d983e9c37598b3dbcefbf848fd348b` is not a destination check.
Anchor's registration preserves both Lean blobs, original Apache notices and
the genuine private ordinary-import client. The [guide](NativeCylinderLimit.md)
states the exact hypotheses and independent gates. No private source text,
incubator dependency or ancestry is imported into release history; leaf acceptance
does not establish aggregate acceptance, official publication or source coverage.

## Chosen native cylinder limits and original-stage sections

`SheafCohomology/NativeCylinderComparison.lean` and its private ordinary-import
client transfer the complete statements **and proof expressions** of accepted
unregistered incubator leaf `139b78367cd641f86c1ccf489f1898db3fab32e4`.
Original worker-b Hive Task `hive-request-f9876d0c2840470583113050ec0546a64eb3954f`
(UID `91e70b6b-63f7-4c56-846f-b66316065a3c`) authored revision
`854e446c6b0efbf85c3023e7b21ccd7f9428d8ea`. Fresh worker-a Task
`hive-request-0b6d132e6ccf9833cd02ade98d31770d2a5ab1e1`
(UID `73f1fb4c-cd23-4deb-afbc-579c3ef3cee7`) reviewed it in
`c2c9ac564f69514bbbebbdd03945c95b19c9f7e9`,
`reviews/native-cylinder-comparison/REVIEW.md`. Anchor reconciled the preserved
author branch with accepted-unregistered parent `bf566ea767083405992cb832df9e914712a9e3cb`
and accepted the leaf at incubator issue #4/comment54410. Donor-only evidence
`da4acd9e9915d3223b5fddbbc297b5702ea264cb` is not a destination check.

Worker-a adapter Task `hive-request-4ea69b252477c9247909ab3e36e3c4b4134edbbb`
(UID `d0fb2e2c-6071-47c1-8e8d-f552d91874a4`) transferred the two Lean leaves
and wrote the standalone guide at `9a00d11039b45e90c6901bd57bb5b2e1fee88306`.
Reversing precisely two producer imports and the client import/namespace/end
recovers donor blobs `76263b70a75ba132e0de4acc3bfe949dfb556457` and
`9c4f0b8bc2a09974a86bba547c191f0decf949de`. Separate target evidence is
`a5c49fc6f3e083b4324d593c1793071afa4fe6e5`. Anchor supplied aggregate imports,
navigation, lifecycle metadata and credit without changing either Lean blob.

The inherited native-cylinder authors, provenance repair, native restriction
author and Andrew Yang's mathlib open-immersion work remain credited above.
The tail-directedness proof expressions adapt worker-b Task
`hive-request-065ffb46d5b6d2b9ada197a66b9c1b783b57e00f`
(UID `4720124c-2740-40ba-947d-5be3c681f64e`), original source commit
`e827107b7a1c6a8cf187189bda816f08931e269a`, retained at
`e266a5076df34934171cc284ba8f2834e56f8c78` in
`FormalFrontier/source-fujiwara-kato-rigid-geometry-i`,
`Research/fk-corollary-3-1-12-open-tail-restriction-scratch.lean:27–49`.
The [standalone guide](NativeCylinderComparison.md) preserves the full
mathematical and contributor boundaries. Apache notices remain intact; no
private source text, incubator dependency or incubator ancestry enters the
deliverable history. Leaf acceptance and focused checks do not accept the
combined graph, release, source correspondence or coverage.
