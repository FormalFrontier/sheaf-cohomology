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

The construction combines the actual-unit equality neighborhood,
one spectral cylinder witness and presheaf naturality. Gluing, a
filtered-colimit comparison and an endpoint isomorphism require separate
results.
