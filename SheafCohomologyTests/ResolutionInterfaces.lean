/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
import SheafCohomology

/-!
# Resolution and local cohomology interfaces

Private clients of quasi-flasqueness, flasque resolution homology, and local
cohomology on opens, coefficient maps, and positive derived pushforwards.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace SheafCohomologyExamples

private theorem setValuedQuasiFlasqueCriterion
    {X : Type u} [TopologicalSpace X]
    (F : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) (Type u)) :
    TopCat.Sheaf.IsQuasiFlasque F ↔
      ∀ (U : Opens X) (_hU : IsCompact (U : Set X)),
        Function.Surjective ((TopCat.Sheaf.restriction U).app F) :=
  TopCat.Sheaf.IsQuasiFlasque.iff_surjective F

private noncomputable def flasqueExtSectionsHomologyIso
    {X : TopCat.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
    [PrespectralSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
    [HasExt.{0} (X.Sheaf AddCommGrpCat.{0})]
    (F : X.Sheaf AddCommGrpCat.{0}) (q : ℕ) :
    (TopCat.Sheaf.flasqueAcyclicResolution F).extZeroComplex.homology q ≅
      (TopCat.Sheaf.flasqueResolutionSections F).homology q :=
  TopCat.Sheaf.flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology F q

private theorem localCohomologyOnOpen
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ) (U : Opens Y) :
    (TopCat.Sheaf.localCohomologyPresheaf f F q).obj (.op U) =
      CategoryTheory.Sheaf.H'
        (show CategoryTheory.Sheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u} from F)
        q ((Opens.map f).obj U) :=
  TopCat.Sheaf.localCohomologyPresheaf_obj f F q U

private theorem localCohomologyCoefficientMap
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    (q : ℕ) {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G)
    (U : Opens Y) :
    ((TopCat.Sheaf.localCohomologyPresheafFunctor f q).map a).app (.op U) =
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) q).map a).app
          (.op ((Opens.map f).obj U)) :=
  TopCat.Sheaf.localCohomologyPresheafFunctor_map_app f q a U

private noncomputable def positiveLocalDerivedComparison
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    (q : ℕ) (hq : 0 < q) :
    TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q :=
  TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyFunctorIsoRightDerived
    f q hq

end SheafCohomologyExamples
