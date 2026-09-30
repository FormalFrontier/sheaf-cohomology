/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original expression and destination adaptation: Formal Frontier Agents.
-/

module
import SheafCohomology.ConePullbackLimitConverse
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Topology.Category.TopCat.Limits.Basic


/-! Arbitrary cocone descent from native limits, with nonidentity index arrows. -/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u v vj wj

namespace SheafCohomologyExamples.ConePullbackLimitConverse

variable (A : Type u) [Category.{w} A]
variable {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]
variable {J : Type wj} [Category.{vj} J]

/-- Import-only client preserving independent coefficient and shape universes. -/
private theorem arbitraryShapeIff (S : Jᵒᵖ ⥤ SheafedSpace A) (C : Cone S)
    (hb : IsLimit ((SheafedSpace.forget A).mapCone C)) :
    Nonempty (IsLimit C) ↔
      Nonempty (IsColimit (SheafedSpace.conePullbackCocone A S C)) :=
  SheafedSpace.nonempty_isLimit_iff_isColimit_conePullbackCocone A S C hb

private def first : (0 : Fin 3) ⟶ (1 : Fin 3) := homOfLE (by decide)
private def second : (1 : Fin 3) ⟶ (2 : Fin 3) := homOfLE (by decide)

private noncomputable def typeConverse (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (C : Cone S) (hb : IsLimit ((SheafedSpace.forget (Type v)).mapCone C))
    (hn : IsLimit C) :
    IsColimit (SheafedSpace.conePullbackCocone (Type v) S C) :=
  SheafedSpace.isColimit_conePullbackCocone_of_isLimit (Type v) S C hb hn

private theorem typeCriterionIff (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (C : Cone S) (hb : IsLimit ((SheafedSpace.forget (Type v)).mapCone C)) :
    Nonempty (IsLimit C) ↔
      Nonempty (IsColimit (SheafedSpace.conePullbackCocone (Type v) S C)) :=
  SheafedSpace.nonempty_isLimit_iff_isColimit_conePullbackCocone (Type v) S C hb

private noncomputable def typeDesc (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (C : Cone S) (hb : IsLimit ((SheafedSpace.forget (Type v)).mapCone C))
    (hn : IsLimit C)
    (K : Cocone (SheafedSpace.conePullback (Type v) S
      ((SheafedSpace.forget (Type v)).mapCone C))) : C.pt.sheaf ⟶ K.pt :=
  (typeConverse S C hb hn).desc K

private theorem typeDesc_first (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (C : Cone S) (hb : IsLimit ((SheafedSpace.forget (Type v)).mapCone C))
    (hn : IsLimit C)
    (K : Cocone (SheafedSpace.conePullback (Type v) S
      ((SheafedSpace.forget (Type v)).mapCone C))) :
    SheafedSpace.sheafMate (Type v) (C.π.app (op (0 : Fin 3))) ≫
      typeDesc S C hb hn K = K.ι.app (0 : Fin 3) :=
  (typeConverse S C hb hn).fac K (0 : Fin 3)

private theorem typeDesc_composite (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (C : Cone S) (hb : IsLimit ((SheafedSpace.forget (Type v)).mapCone C))
    (hn : IsLimit C)
    (K : Cocone (SheafedSpace.conePullback (Type v) S
      ((SheafedSpace.forget (Type v)).mapCone C))) :
    (SheafedSpace.conePullback (Type v) S
      ((SheafedSpace.forget (Type v)).mapCone C)).map (first ≫ second) ≫
      SheafedSpace.sheafMate (Type v) (C.π.app (op (2 : Fin 3))) ≫
      typeDesc S C hb hn K = K.ι.app (0 : Fin 3) := by
  exact (congrArg (· ≫ typeDesc S C hb hn K)
    (SheafedSpace.conePullbackCocone_triangle (Type v) S C (first ≫ second))).trans
      (typeDesc_first S C hb hn K)

private theorem typeDesc_unique (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (C : Cone S) (hb : IsLimit ((SheafedSpace.forget (Type v)).mapCone C))
    (hn : IsLimit C)
    (K : Cocone (SheafedSpace.conePullback (Type v) S
      ((SheafedSpace.forget (Type v)).mapCone C)))
    (d : C.pt.sheaf ⟶ K.pt)
    (hd : ∀ i : Fin 3, SheafedSpace.sheafMate (Type v) (C.π.app (op i)) ≫
      d = K.ι.app i) : d = typeDesc S C hb hn K := by
  apply (typeConverse S C hb hn).uniq K d
  exact hd

private noncomputable def additiveConverse (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (C : Cone S) (hb : IsLimit ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C))
    (hn : IsLimit C) :
    IsColimit (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S C) :=
  SheafedSpace.isColimit_conePullbackCocone_of_isLimit AddCommGrpCat.{v} S C hb hn

private theorem additiveCriterionIff (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (C : Cone S) (hb : IsLimit ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C)) :
    Nonempty (IsLimit C) ↔
      Nonempty (IsColimit (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S C)) :=
  SheafedSpace.nonempty_isLimit_iff_isColimit_conePullbackCocone AddCommGrpCat.{v} S C hb

private noncomputable def additiveDesc (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (C : Cone S) (hb : IsLimit ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C))
    (hn : IsLimit C)
    (K : Cocone (SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C))) : C.pt.sheaf ⟶ K.pt :=
  (additiveConverse S C hb hn).desc K

private theorem additiveDesc_last (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (C : Cone S) (hb : IsLimit ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C))
    (hn : IsLimit C)
    (K : Cocone (SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C))) :
    SheafedSpace.sheafMate AddCommGrpCat.{v} (C.π.app (op (2 : Fin 3))) ≫
      additiveDesc S C hb hn K = K.ι.app (2 : Fin 3) :=
  (additiveConverse S C hb hn).fac K (2 : Fin 3)

private theorem additiveDesc_composite (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (C : Cone S) (hb : IsLimit ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C))
    (hn : IsLimit C)
    (K : Cocone (SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C))) :
    (SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C)).map (first ≫ second) ≫
      SheafedSpace.sheafMate AddCommGrpCat.{v} (C.π.app (op (2 : Fin 3))) ≫
      additiveDesc S C hb hn K = K.ι.app (0 : Fin 3) := by
  exact (congrArg (· ≫ additiveDesc S C hb hn K)
    (SheafedSpace.conePullbackCocone_triangle AddCommGrpCat.{v} S C (first ≫ second))).trans
      ((additiveConverse S C hb hn).fac K (0 : Fin 3))

private theorem additiveDesc_unique (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (C : Cone S) (hb : IsLimit ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C))
    (hn : IsLimit C)
    (K : Cocone (SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C)))
    (d : C.pt.sheaf ⟶ K.pt)
    (hd : ∀ i : Fin 3, SheafedSpace.sheafMate AddCommGrpCat.{v} (C.π.app (op i)) ≫
      d = K.ι.app i) : d = additiveDesc S C hb hn K := by
  apply (additiveConverse S C hb hn).uniq K d
  exact hd

private def emptyDiagram : PEmptyᵒᵖ ⥤ SheafedSpace (Type 0) where
  obj := fun i ↦ nomatch i
  map := fun {i} ↦ nomatch i

private def emptyVertex (F : (TopCat.of PUnit.{1}).Sheaf (Type 0)) :
    SheafedSpace (Type 0) where
  carrier := TopCat.of PUnit.{1}
  presheaf := F.1
  IsSheaf := F.2

private def emptyNativeCone (F : (TopCat.of PUnit.{1}).Sheaf (Type 0)) :
    Cone emptyDiagram where
  pt := emptyVertex F
  π := {
    app := fun i ↦ nomatch i
    naturality := by
      intro i
      exact nomatch i }

private noncomputable def emptyBaseIsLimit (F : (TopCat.of PUnit.{1}).Sheaf (Type 0)) :
    IsLimit ((SheafedSpace.forget (Type 0)).mapCone (emptyNativeCone F)) where
  lift := fun Q ↦ TopCat.isTerminalPUnit.from Q.pt
  fac := by
    intro Q i
    exact nomatch i
  uniq := by
    intro Q m hm
    exact TopCat.isTerminalPUnit.hom_ext _ _

/-- The necessary direction for an empty diagram: the native terminal witness
is explicitly supplied, independently of any sheaf-initiality witness. -/
private noncomputable def emptyNecessary (F : (TopCat.of PUnit.{1}).Sheaf (Type 0))
    (hn : IsLimit (emptyNativeCone F)) :
    IsColimit (SheafedSpace.conePullbackCocone (Type 0) emptyDiagram
      (emptyNativeCone F)) :=
  SheafedSpace.isColimit_conePullbackCocone_of_isLimit (Type 0)
    emptyDiagram (emptyNativeCone F) (emptyBaseIsLimit F) hn

end SheafCohomologyExamples.ConePullbackLimitConverse
