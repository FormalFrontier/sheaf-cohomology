# Forgetting native additive cone cocones

Import `SheafCohomology.AbelianForget.ConePullbackCocone` for the three public
declarations in `AlgebraicGeometry.SheafedSpace.AbelianForget`. This focused
module publicly imports `SheafCohomology.AbelianForget.ConePullback` and
`SheafCohomology.ConePullbackCocone`. The aggregate `SheafCohomology`
re-exports it; the examples root imports its private client module.

Take any `J : Type wj` with `[Category.{vj} J]`, a diagram
`S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v}`, and an **actual** native cone
`c : Cone S`. Let `cA := (SheafedSpace.forget AddCommGrpCat.{v}).mapCone c`,
`cT := underlying.mapCone c`, `U := underlyingSheaf (c.pt : TopCat)`, and
`θ := conePullbackIso S cA`. The independent index object and morphism
universes are `wj` and `vj`; `v` is the sheaf/coefficient universe.

- `underlying_mapCone_forget S c` identifies
  `(SheafedSpace.forget (Type v)).mapCone cT = underlyingCone S cA`
  *strictly*, by `rfl`. The vertex and projection arrows are unchanged.
- `conePullbackCocone_forget_ι S c i`, for any `i : J`, identifies the
  Type-valued native cocone leg with
  `θ.hom.app i ≫ U.map ((SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app i)`.
  Here the Type-valued cocone is
  `SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying) cT`.
  The stage law uses the mate of the *actual* projection `c.π.app (op i)`.
- `conePullbackCocone_forget_desc S c` needs precisely three ordinary
  colimit witnesses: `[HasColimit DA]`, `[HasColimit (DA ⋙ U)]`, and
  `[HasColimit DT]`, where
  `DA := SheafedSpace.conePullback AddCommGrpCat.{v} S cA` and
  `DT := SheafedSpace.conePullback (Type v) (S ⋙ underlying)
    ((SheafedSpace.forget (Type v)).mapCone cT)`.
  Writing `KA := SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c`
  and `KT := SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying) cT`,
  its exact canonical comparison equation is:

  ```text
  (colimMap θ.hom ≫ colimit.post DA U) ≫ U.map (colimit.desc DA KA)
    = colimit.desc DT KT.
  ```

The private `conePullbackCocone_forget_desc_canonical` transports the actual
diagram colimit witnesses to the canonical pullback comparison and proves the
desc equation by `colimit.post_desc`, `colimit.map_desc`, `colimit.hom_ext`,
`colimit.ι_desc`, and the stage law. No colimiting cocone, limiting native
cone, filteredness, nonempty index, stage isomorphism, or endpoint
invertibility is assumed or obtained. The private import-only clients in
`SheafCohomologyExamples.AbelianForgetConePullbackCocone` exercise all three
`Fin 3` stages, two nonidentity **index** arrows, the three explicit colimit
witnesses, and a native cone with literal empty carrier. Their local
same-universe filtered specialization establishes invertibility only of
`colimMap θ.hom ≫ colimit.post DA U`, using existing results; arrow images
may still be identities and neither desc-to-vertex map is claimed invertible.
