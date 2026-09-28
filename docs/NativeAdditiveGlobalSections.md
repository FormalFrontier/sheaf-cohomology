# Native additive global sections of filtered spectral limits

For a small category `J`, an additive sheafed-space diagram
`S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat`, and **any chosen cone** `m : Cone S`,
`AlgebraicGeometry.SheafedSpace.nativeAdditiveGlobalSectionsCocone S m`
has vertex `Γ.obj (op m.pt)` and leg at `i : J` exactly
`Γ.map (m.π.app (op i)).op`. Its naturality is the triangle identity of `m`;
no limiting or spectral assumption is used. The morphism
`nativeAdditiveGlobalSectionsComparison S m` is the additive colimit's
`colimit.desc` of this cocone. The theorem
`colimit_ι_nativeAdditiveGlobalSectionsComparison S m i` identifies the
composite of the original stage coprojection with the comparison as the
global-section map of the original cone projection. The inferred signatures
of the cocone, comparison and stage law do not require `IsFiltered J`, a
limit witness `hm`, or spectral hypotheses, even though their source module
declares filteredness for its later isomorphism theorem.

If `J` is filtered, `hm : IsLimit m`, every original stage space of
`S ⋙ SheafedSpace.forget AddCommGrpCat` is spectral, and every original
transition of that space diagram is a spectral map, then
`isIso_nativeAdditiveGlobalSectionsComparison S m hm hstage htransition`
proves the comparison is an isomorphism. There is **no** assumption of
surjective transitions, injective projections, an already-invertible map,
nonempty opens, or an independently supplied limit of restrictions. The
statement keeps the original cone, including its original projections.

The proof first obtains a limiting space cone by applying
`SheafedSpace.preservesLimitForgetOfHasLimit` to `hm`. It obtains a Type-valued
native limiting cone independently from
`SheafedSpace.AbelianForget.preservesCofilteredLimit S`; the official
`underlying_mapCone_forget` and `underlyingDiagram_forget` identify the full
space cones and functors, not just their carrier objects. Let `Q` be
`limitConeOfSpaceCone` of the forgotten diagram and actual space cone. The
unique cone-point iso `e : underlying.obj m.pt ≅ Q.cone.pt` satisfies
`e.inv ≫ (underlying.mapCone m).π.app (op i) = Q.cone.π.app (op i)`.

On sections, the identity-component natural iso
`nativeAdditiveGammaDiagramForgetIso` (kept private) compares the forgotten
additive Γ diagram with the actual Type Γ diagram. Its components reduce,
by `Γ_obj_op` and `underlying_obj_presheaf`, to the same `op ⊤` sections.
Naturality and the projection case reduce, by `Γ_map_op`,
`underlying_map_c`, and the component of `whiskerRight`, to the underlying
map of the **original** additive `f.hom.c.app (op ⊤)`; the Lean proof
exhibits this common component before applying reflexivity. Thus the
identity-on-sections iso at `m.pt` and the diagram iso transport original
projections without substituting another cone.

Let `A = S.rightOp ⋙ Γ`, `F = forget AddCommGrpCat`, `N = S ⋙ underlying`,
`D = N.rightOp ⋙ Γ`, `q` be the diagram-induced colimit iso, and `t` the
vertex section iso. The Type-valued arrow compared to the existing native
Type comparison is

```text
q.inv ≫ colimit.post A F ≫ F.map (nativeAdditiveGlobalSectionsComparison S m)
  ≫ t.hom ≫ Γ.map e.inv.op.
```

The *forward* direction of `colimit.post` is essential. Colimit extensionality
reduces equality to each stage: `HasColimit.ι_isoOfNatIso_inv_assoc`,
`colimit.ι_post_assoc`, and the new additive stage law yield the forgotten
actual projection; the section-map compatibility turns it into the Type
projection; `e.inv` turns it into `Q`'s projection. The already-proved
`isIso_nativeGlobalSectionsComparison N c hc` supplies the Type isomorphism;
filtered colimit preservation by `F` and reflection of isomorphisms by `F`
cancel the other comparison isomorphisms. This proof does not repeat the
underlying spectral, compactness, gluing, or local section arguments.

`SheafCohomologyExamples.NativeAdditiveGlobalSections` is an
ordinary-import client. Its theorem `nativeProjection_eq_iff_eventually_eq`
states that two sections at one *original* additive stage agree under the
original projection to `m.pt` if and only if an original transition sends
them to equal sections at some later stage. Its proof applies the new
comparison's injectivity and exact stage law; the explicit
`isColimitOfPreserves` witness for `F.mapCocone` then invokes
`Types.FilteredColimit.isColimit_eq_iff'` on the forgotten actual colimit.
Conversely it maps the resulting equality of original additive
coprojections through the new comparison. No eventual-equality hypothesis
is fed into this client.

## Reproduction and status

The original two Lean modules were accepted as **unregistered incubator code**
by Anchor at incubator issue #4/comment 54912 on 2026-09-27, following the
independent review at `69190f94af343224a2b179f93a228a273758b185`.
This transfer adapts their exact code revision
`4806e203844ff4f4abbcf06d35a93b25a5fbf814`, not an incubator main or
official dependency. Its destination base
`a67d8f00d6da10ccd6af1beebe04be053fcdc1cd` is **unaccepted** as of
this adapter's frozen 2026-09-27 snapshot. At that snapshot the separate adapter was
**unreviewed, unaccepted and unregistered**; the donor review does not approve
the destination, and changes to the frozen base may require rework. The
unchanged 11-object destination manifest pins Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`,
spectral-stone-duality `452b7b7be1bea76434cd083b1019a26f96b4ab30`,
and ideal `001e3b7508184ecd51e0d86177cb1d54508bf59d`.
From the destination project root, with those pinned inputs:

```sh
lake exe cache get
env LEAN_NUM_THREADS=2 lake --wfail build +SheafCohomology.NativeAdditiveGlobalSections:olean +SheafCohomologyExamples.NativeAdditiveGlobalSections:olean
```

The focused adapter intentionally omitted root imports. Anchor's subsequent
source-only 83-module registration adds the producer to `SheafCohomology` and
the ordinary client to `SheafCohomologyExamples`, without changing either Lean
blob. At that dated registration, this destination candidate remained unreviewed
and unaccepted; full combined checks and predecessor releases were separate
gates. The focused build and
actual-generating-module transitive axiom census of **both** new Lean modules,
including private/generated declarations, are stored separately under
`docs/evidence/native-additive-sheaf-adapter-9c8d00ee/` on the evidence-only
branch, bound to the final uninstrumented code revision; the donor's separate
incubator evidence remains distinct. Subsequent scoped destination review
`7f48d057eefdb811782bbadce2ccacceb2ed9ae6` approved the mathematical/API/
provenance/registration increment; full 83-module CI627 on
`70d1aad387e72104ae294ac07a32c113d7f72e75` succeeded on 2026-09-27
at 22:47:17 UTC and its complete both-target/private-inclusive evidence was
owner-intaken. The later actual 81-module predecessor was separately accepted and
officially published at `b743039857ca8c206b6a8cdb99afe7c7e8ce0c25`, verified
on 2026-09-28 at 02:39:17 UTC. The earlier 83 reconciliation merged its
accepted main `6e055c187a6e097636f2e9b5bf5d4f5eba351876`.

That reconciliation made a reversible header-only credit repair in both
new modules: `Authors: Formal Frontier Agents`, followed by `Contributor:`
retaining the donor author's ENTIRE original Task/UID text. Remove that new
Authors line and change Contributor back to Authors to recover the previous
whole file; then the historical import/namespace substitutions recover the
donor. Every byte from `module` onward, both roots, all 81 other Lean blobs and
eleven whole pins remained fixed relative to the original 83 assembly. Earlier
exact-header and whole-blob statements
apply to the historical adapter/registration, not this header-repaired source.
The changed source digest passed full CI666 with complete owner intake, followed
by fresh independent final review and separate owner main/prep/public decisions.
Actual accepted 83 main/release-prep
`9ba31ec9d399343a81e7284f7856f53c6a1d7f5c` and its official private
GitHub release `6793f2ff8469d1cab23a98ac2da22a3286d22f8e` (verified on
2026-09-28 at 05:15:05 UTC) complete the 83 gates, not 84 acceptance. This
84 successor carried both accepted83 credit headers unchanged. Its separate
generic restriction producer and additive restriction client header changes
make original84 CI637 historical evidence, not a pass for the successor;
applicable full84 successor CI and independent final main/prep/public review
were outstanding at that dated checkpoint. Full changed-input CI674,
independent final review and distinct owner decisions subsequently supported
actual accepted84 main `36e49294f84208fa678872e84b6bdbd96c603188` and
official private release `e5d7d6e60243da2ec9a2af243fac3f3a3bf7dc37`,
verified on 2026-09-28 (issue #34/comment 56186). This **unaccepted 85**
successor inherits both whole 83 credit repairs through accepted84; its
module-onward bytes remain frozen 85. The original 85 CI655 does not cover
the four inherited changed headers: applicable successor85 both-target/
private-inclusive checks and consolidated independent final review remain.
Source correspondence stays separate.
Neither this focused adapter nor the Type-only compact-cylinder result claims
an additive-cylinder extension or a source-specific endpoint.

## Expression provenance

- New additive cocone, original-cone comparison, Γ forgetting iso, cone-iso
  transport, filtered-colimit argument, and client expression: worker-a Hive
  Task `hive-request-0b67e8c17f9041202a7550e7a7703f53d6bb4004`, UID
  `7b289efe-e184-4c33-9723-7ef39e977b59`.
- The source-only, noncompiled proof plan and dependency boundary were prepared
  by worker-a Hive Task `hive-request-7a9932f81650d59ba53a99f18bb87a61b1e5046d`,
  UID `117c1001-76ff-46a7-863b-fefcb485badb`, at report commit
  `0b33b9cf70c50509ca766a020cd82667e7cf16e1`.
- The additive cocone shape, `colimit.desc`/stage law, and the Type comparison
  invocation closely adapt `NativeLimitGlobalSections.lean`, author worker-b
  Hive Task `hive-request-4c216dbec01d4be3c9179c965656f0054d638fb8`,
  UID `b5bc6fa6-d9ab-4cfa-bd79-3ec1cdf7265a`.
  The Type-level compact/spectral and sheaf proof expressions are invoked,
  **not copied**.
- The full-cone additive-forget preservation witness is invoked from the
  official `SheafCohomology.AbelianForget.LimitPreservation` by worker-b Hive
  Task `hive-request-13fb7168e78b10adc0a739488a5b88a5bad2cd58`, UID
  `9a8d7368-37db-444c-b740-2b889ce82678`; its mate or sheaf proof
  expression is **not copied**. The separate official
  `SheafCohomology.LimitPreservation` result is likewise invoked, not copied.
- The Γ definition and equations come from mathlib's Kim Morrison;
  the filtered-Type-colimit equality from Kim Morrison and Reid Barton;
  filtered commutative-group colimits from Justus Springer; the general
  colimit-iso identities from Reid Barton, Mario Carneiro, Kim Morrison, and
  Floris van Doorn. These upstream theorems are invoked, not reimplemented.
- This import/namespace adapter and standalone destination guide are by
  worker-a Hive Task `hive-request-6d69256f4facbc79af9be1ed2e70a55908a11731`,
  UID `9c8d00ee-de21-4aef-8927-357aeec5a8af`. The two original Apache-2.0
  SPDX/Authors headers at that historical adapter belonged to the donor proof
  author, not this adapter. Anchor's subsequent collective-credit repair
  preserves that entire original Contributor text and all expressions; it
  claims no proof authorship.
