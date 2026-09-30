<!-- SPDX-License-Identifier: Apache-2.0 -->

# Local sections of inverse-image sheaves

Import `SheafCohomology.PullbackLocalSections`. Given arbitrary
`X Y : TopCat.{v}`, `f : X ⟶ Y` and `F : Y.Sheaf (Type v)`, the results use
the **actual** sheaf `P := (TopCat.Sheaf.pullback (Type v) f).obj F` and
the **actual** adjunction unit
`η := (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F`.
Here `η.hom.app (op V)` sends an `F`-section on `V : Opens Y` to a
`P`-section on `f ⁻¹' V` (`(Opens.map f).obj V` in Lean).

## Stalks and local sections

* `TopCat.Sheaf.PullbackLocalSections.stalkIso f F x` is an isomorphism
  `F.presheaf.stalk (f x) ≅ P.presheaf.stalk x`, whose forward morphism is
  **literally** the stalk-functor map of `η.hom`, followed by mathlib's
  `stalkPushforward`. `germ_stalkIso` identifies its action on a target germ
  with the germ of the actual-unit section. No model-dependent comparison is
  needed by clients.
* `exists_local_representation f F s hx` represents `s : P(U)` near
  `x ∈ U`: it produces opens `V ⊆ Y` and `W ⊆ X` with `f x ∈ V`,
  `x ∈ W ⊆ U ∩ f ⁻¹' V`, and `a : F(V)` such that
  `(η_V(a))|W = s|W`.
* `exists_target_eq_neighborhood f F V U hU a b heq` reflects equality
  `(η_V(a))|U = (η_V(b))|U` to a single target open `V' ⊆ V` containing
  `f(U)` on which `a|V' = b|V'`. It also works for the empty `U`.
  No compactness, spectrality, surjectivity, or other condition on `f` is
  required. The open `V'` is the union of target neighborhoods witnessing
  equality of the germs of `a` and `b`; sheaf separatedness combines them.
* `exists_finite_compact_representation f F hU s` assumes only
  `[PrespectralSpace X]` and compactness of the *source* open `U`. It
  produces a `Finset U` of compact-open neighborhoods `Wᵢ ⊆ U` covering
  `U`, target opens `Vᵢ`, and target sections `aᵢ : F(Vᵢ)` with
  `Wᵢ ⊆ f ⁻¹' Vᵢ` and `(η_(Vᵢ)(aᵢ))|Wᵢ = s|Wᵢ`. It includes an empty
  finite cover when `U` is empty. The chosen target opens need not be compact.

The ordinary public client module
`SheafCohomologyExamples.PullbackLocalSections` gives four named theorems:
`native_unit_germ_reflects`, `native_unit_germs_locally_represented`,
`native_equalizer_open`, and `native_finite_target_germ_cover`. They derive
germ reflection, a neighborhood on which *every* germ of a section is
represented by one native-unit section, an equalizer neighborhood, and a finite
family of target sections representing all germs on a compact source open.

## Proof and boundaries

Mathlib already proves the **presheaf** `stalkPullbackIso`; this module
does not reprove it. The proof compares the chosen sheaf adjunction with the
constructed left-Kan-extension/sheafification adjunction via
`Adjunction.unit_leftAdjointUniq_hom_app` and `TopCat.Sheaf.pullbackIso`.
It then factors the actual stalk map through the existing presheaf
isomorphism, the stalk-isomorphism of the actual `toSheafify` unit, and
the comparison isomorphism. Germ representation and equality use mathlib's
`exists_germ_eq`, `germ_eq`, and `section_ext`. The finite cover refines to
the compact-open basis and invokes a compact finite subcover.

There is no global section surjectivity, diagram-colimit or endpoint theorem
here, and no new local-lift or transition structure. The producer imports only
mathlib, not incubator or source-repository experiments; its public API has no
source-research prerequisite. Neither a spectral-map hypothesis, inhabitedness
nor surjectivity is needed.
