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

## Attribution and lifecycle

The original mathematical and Lean implementation was authored by worker-b
Hive Task `hive-request-c862e7aa8f5b10a37f55dbfbfcc07250a83772cd`
(UID `0b29aa2c-31b4-4085-b8ae-dfec0cb71756`), accepted as the
**unregistered** incubator leaf at
`9cba716e58ac499e102abfadeccd811d1b0c23cf`. Independent source and
module review is recorded at
`af4468a1593d2c2a75320324352d51b0e4a886b0` in
`reviews/pullback-local-sections/REVIEW.md`, by worker-a Hive Task
`hive-request-7708ef819d1da79f05079e569149a3a3b5fbcfe5`
(UID `10306134-381d-434b-ab66-8077fb2a93da`). The transfer and
destination-specific guide/client adaptation are by a distinct worker-a Hive
Task `hive-request-6a01a72d5e80988d20b9716dc7419592c896c3a4`
(UID `dcf69e1a-2f1d-43ba-8000-b176eb638e64`), not by the reviewer.

In particular, the producer's private `constructed_unit_hom` proof closely
adapts the **expression** (`change`/`simp`/`rfl`), not just the mathematical idea,
of Anchor's `sheafPullbackConstruction_unit_app_hom` from source research revision
`e266a5076df34934171cc284ba8f2834e56f8c78`, file
`Research/fk-proposition-3-1-10-stage-section-transport-probe.lean` around
line 219 (blob `939e35949d83eb00f63856f702ed93dd9c7fff66`).
This is proof-expression credit, not a source import or source-coverage claim.

The adapter was an unregistered candidate on frozen **UNACCEPTED** parent
`6ec75cd4c22f74e2607adf92d85b5caa30087ca7` when assigned. That historical
dependency state is preserved in its report. The parent has since been
independently reviewed, accepted and integrated after complete 63-module
CI469 evidence, then verified on official GitHub at
`32b1fb7787d5036c8b7181565a22a460b160f91d` with the same tree.
Anchor now registers the two unchanged leaves in the aggregate production and
ordinary-client roots, forming a source-only 65-module **candidate**, not a
fully accepted graph. The leaf's focused build and complete destination-module
axiom census are documented in the separate evidence branch and owning issue #34;
neither focused success nor the prior incubator review accepts these changed
aggregate inputs. Exact final destination/release review, applicable combined
build and private-inclusive axiom evidence, owner acceptance, integration,
verified publication and later reviewed incubator replacement remain separate.
No source-coverage decision is claimed here.
