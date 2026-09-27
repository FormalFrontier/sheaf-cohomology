<!-- SPDX-License-Identifier: Apache-2.0 -->

# Native stage-section equality

Import `SheafCohomology.NativeStageSectionEquality`. Let
`J : Type v` be a small filtered category,
`N : Jᵒᵖ ⥤ SheafedSpace (Type v)`, and
`c : Cone (N ⋙ SheafedSpace.forget (Type v))` an **actual** limiting cone.
Assume spectral underlying stage spaces and spectral underlying transition
maps. Neither stages nor maps need to be inhabited or surjective.

* `AlgebraicGeometry.SheafedSpace.exists_stage_eq_of_pullback_unit_eq`
  takes a compact open `V` of `N.obj (op i)` and native sections `a,b` on
  `V`. If the actual `TopCat.Sheaf.pullbackPushforwardAdjunction` unit along
  `c.π.app (op i)` gives equal sections on the inverse image of `V`, then
  there are `j : J` and `g : i ⟶ j` such that the **native** morphism
  `(N.map g.op).hom.c.app (op V)` takes `a` and `b` to equal sections on
  the *whole* inverse image of `V` at `j`.
* `AlgebraicGeometry.SheafedSpace.exists_Γ_eq_of_pullback_unit_eq` gives
  the whole-space specialization. Its conclusion is literal equality under
  `(N.rightOp ⋙ SheafedSpace.Γ).map g`, the existing functor, with no new
  stage-section functor.

The producer combines the actual-unit equality-neighborhood theorem from
`SheafCohomology.PullbackLocalSections` with the published
`SpectralStoneDuality.limitCylinder_subset_iff_eventually`. The first gives
an arbitrary (not necessarily compact) target open `E ⊆ V` where the two
sections agree, while the projection inverse image of `V` lies in that of
`E`. The cylinder criterion makes these inverse-image opens coincide at
one stage over `op i`. Naturality of the actual native presheaf morphism
transports equality on `E`; the restriction along the resulting equality
of stage opens is an isomorphism and can be canceled. At `⊤`, the result
uses mathlib's `SheafedSpace.Γ_map_op` for the *existing* functor.

The ordinary public-import client in
`SheafCohomologyExamples.NativeStageSectionEquality` derives two
contrapositive distinguishability statements, one for compact opens and
one for transitions of the literal existing global-section functor.

This leaf does not prove sheaf gluing, finite simultaneous equality,
filtered-colimit comparison or an endpoint isomorphism. It makes no
source-correspondence or source-coverage claim. The accepted local-unit
input is incubator `9cba716e58ac499e102abfadeccd811d1b0c23cf`
(review `af4468a1593d2c2a75320324352d51b0e4a886b0`); the native pullback
input is the unchanged `SheafCohomology.PullbackLocalSections` module
(blob `c2b75be93eaff5bdbc9449f7412c759f2733cac5`) promoted from that
accepted incubator parent; the topology input is the official published
`spectral-stone-duality` commit
`452b7b7be1bea76434cd083b1019a26f96b4ab30`, inheriting official
`ideal-completion` `001e3b7508184ecd51e0d86177cb1d54508bf59d`.
This newer spectral-stone-duality release replaces the incubator source's
original dependency on `5e2cf4120087d32b1456e0244de46741d85dc83d`;
the unchanged cylinder API is checked afresh against the destination graph.

Mathematical motivation and whole-stage equality-reflection design come
from Anchor (Source Maintainer),
`source-fujiwara-kato-rigid-geometry-i` at
`e266a5076df34934171cc284ba8f2834e56f8c78`,
`Research/fk-proposition-3-1-10-whole-stage-equality-reflection-probe.lean`
(blob `f46040d3130b3fab7f8947d41ac6542db6764750`) and its matching
guide. That earlier source-local proof uses a compact intermediate witness,
an explicit limit and an additional pullback-section system; no proof
expression from that earlier source-local probe was adapted in the original
native producer. This native proof instead combines one actual-unit
equality neighborhood, one cylinder witness and presheaf naturality.
Authored by worker-b Hive Task
`hive-request-83333dedd640d855f159f1c115a70d659ba2c7dc`
(UID `ce8bbfcb-4d1f-4e5f-b043-5ec831bc6bcd`), incubator
`c7818152bd5ebef3d768de238962bf9fc04fb7fc` (tree
`4b21cb1f3508f815b001bc73fd9c6a38c3f61547`), reviewed independently
by worker-a Hive Task
`hive-request-a44553406806c535fda284689c5428b6e55f00ff` (UID
`54ee6779-5591-4608-b802-3906536cc1a7`; full review
`9419e5f00d105a682c613d75ec6f42f724e7aa05`).
The **full producer and client proof expressions are copied and mechanically
transferred**, not merely their mathematical ideas, by worker-a Hive Task
`hive-request-ff998c4cc73fa7cfcec2d169e68b78c8e14c7e0a` (UID
`d11b0afb-7e2c-44a8-b31c-78fe5a3637f7`). Only the producer import and
client import/namespace change; their reverse substitutions reproduce the
original two Lean blobs `cbc6ebe0b1de22a941f373c550d92d6d2579259a`
and `e14d0b3ada7690fb1d43f9704d472afc10712203`.

The producer and ordinary client are registered in `SheafCohomology` and
`SheafCohomologyExamples`, respectively. This source-only 67-module assembly
preserves their Lean expressions and the adapter's eleven-package graph.
Focused destination checks do not certify the changed aggregate roots;
applicable combined build and private-inclusive standard-axiom evidence,
fresh final independent review, owner acceptance, protected integration and
verified official release remain required. It is not
an endpoint isomorphism, a source-coverage decision or a reviewed incubator
replacement.
