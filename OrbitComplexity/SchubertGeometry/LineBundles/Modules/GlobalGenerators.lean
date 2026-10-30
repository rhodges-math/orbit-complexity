import Batteries.Tactic.OpenPrivate
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalMonomials
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.ModuleLocality

/-! # Ordinary global generators of the specified transition module -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
noncomputable section
universe u v w

namespace SchubertGeometry.ProjectiveLine
open SchubertGeometry.ProjectiveLine
open private structureModule line affine chart unit_top_ext
  monomial_left_value monomial_right_value from
  OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalMonomials
attribute [local instance] MvPolynomial.gradedAlgebra

private def sectionCoprodDesc {D : Type v} [Category.{w} D]
    {A B E : D} [HasBinaryCoproduct A B] (f : A ⟶ E) (g : B ⟶ E) :
    A ⨿ B ⟶ E :=
  coprod.desc f g

private theorem sectionCoprodDesc_inl {D : Type v} [Category.{w} D]
    {A B E : D} [HasBinaryCoproduct A B] (f : A ⟶ E) (g : B ⟶ E) :
    coprod.inl ≫ sectionCoprodDesc f g = f :=
  coprod.inl_desc f g

private theorem sectionCoprodDesc_inr {D : Type v} [Category.{w} D]
    {A B E : D} [HasBinaryCoproduct A B] (f : A ⟶ E) (g : B ⟶ E) :
    coprod.inr ≫ sectionCoprodDesc f g = g :=
  coprod.inr_desc f g

/-- The endpoint monomials define an ordinary two-generator evaluation map. -/
def projectiveOrdinaryEval (C : Type u) [CommRing C] (d : ℕ) :
    (structureModule (line C) ⨿ structureModule (line C)) ⟶
      SchubertGeometry.ProjectiveLine.projectiveTransitionModule C d :=
  sectionCoprodDesc (D := (line C).Modules)
    (projectiveMonomialSection C d 0 (Nat.zero_le _))
    (projectiveMonomialSection C d d le_rfl)

private theorem ordinaryEval_inl (C : Type u) [CommRing C] (d : ℕ) :
    coprod.inl ≫ projectiveOrdinaryEval C d =
      projectiveMonomialSection C d 0 (Nat.zero_le d) :=
  sectionCoprodDesc_inl (projectiveMonomialSection C d 0 (Nat.zero_le d))
    (projectiveMonomialSection C d d le_rfl)

private theorem ordinaryEval_inr (C : Type u) [CommRing C] (d : ℕ) :
    coprod.inr ≫ projectiveOrdinaryEval C d =
      projectiveMonomialSection C d d le_rfl :=
  sectionCoprodDesc_inr (projectiveMonomialSection C d 0 (Nat.zero_le d))
    (projectiveMonomialSection C d d le_rfl)

private theorem cancelIsoInv {D : Type*} [Category D] {A B E : D}
    (e : A ≅ B) {f g : A ⟶ E} (h : e.inv ≫ f = e.inv ≫ g) : f = g := by
  calc
    f = e.hom ≫ (e.inv ≫ f) := (e.hom_inv_id_assoc f).symm
    _ = e.hom ≫ (e.inv ≫ g) := by rw [h]
    _ = g := e.hom_inv_id_assoc g

private theorem unitIso_inv_hom_top {X : Scheme.{u}} {M : X.Modules}
    (e : M ≅ structureModule X) :
    (((e.inv ≫ e.hom).val.app (.op ⊤)).hom (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) := by
  exact congrArg (fun f : structureModule X ⟶ structureModule X =>
    (f.val.app (.op ⊤)).hom (1 : Γ(X, ⊤))) e.inv_hom_id

private theorem leftEndpoint (C : Type u) [CommRing C] (d : ℕ) :
    (Scheme.Modules.restrictFunctor (chart C ⟨0⟩)).map
        (projectiveMonomialSection C d 0 (Nat.zero_le _)) ≫
          (SchubertGeometry.ProjectiveLine.projectiveTransitionChart C d ⟨0⟩).hom =
      (Scheme.Modules.restrictUnitIso (chart C ⟨0⟩)).hom := by
  apply cancelIsoInv (Scheme.Modules.restrictUnitIso (chart C ⟨0⟩))
  apply unit_top_ext
  have hu : (((Scheme.Modules.restrictUnitIso (chart C ⟨0⟩)).inv).val.app (.op ⊤)).hom
      (1 : Γ(affine C, ⊤)) = (1 : Γ(line C, chart C ⟨0⟩ ''ᵁ ⊤)) := by
    change ((chart C ⟨0⟩).appIso ⊤).inv 1 = 1
    exact map_one _
  change ((SchubertGeometry.ProjectiveLine.leftChartMap C d).val.app (.op ⊤)).hom
    (((projectiveMonomialSection C d 0 (Nat.zero_le _)).val.app
      (.op (chart C ⟨0⟩ ''ᵁ ⊤))).hom
        ((((Scheme.Modules.restrictUnitIso (chart C ⟨0⟩)).inv).val.app (.op ⊤)).hom
          (1 : Γ(affine C, ⊤)))) = _
  rw [hu, monomial_left_value]
  exact (show (Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ 0) =
    (1 : Γ(affine C, ⊤)) by simp).trans
      (unitIso_inv_hom_top (Scheme.Modules.restrictUnitIso (chart C ⟨0⟩))).symm

private theorem rightEndpoint (C : Type u) [CommRing C] (d : ℕ) :
    (Scheme.Modules.restrictFunctor (chart C ⟨1⟩)).map
        (projectiveMonomialSection C d d le_rfl) ≫
          (SchubertGeometry.ProjectiveLine.projectiveTransitionChart C d ⟨1⟩).hom =
      (Scheme.Modules.restrictUnitIso (chart C ⟨1⟩)).hom := by
  apply cancelIsoInv (Scheme.Modules.restrictUnitIso (chart C ⟨1⟩))
  apply unit_top_ext
  have hu : (((Scheme.Modules.restrictUnitIso (chart C ⟨1⟩)).inv).val.app (.op ⊤)).hom
      (1 : Γ(affine C, ⊤)) = (1 : Γ(line C, chart C ⟨1⟩ ''ᵁ ⊤)) := by
    change ((chart C ⟨1⟩).appIso ⊤).inv 1 = 1
    exact map_one _
  change ((SchubertGeometry.ProjectiveLine.rightChartMap C d).val.app (.op ⊤)).hom
    (((projectiveMonomialSection C d d le_rfl).val.app
      (.op (chart C ⟨1⟩ ''ᵁ ⊤))).hom
        ((((Scheme.Modules.restrictUnitIso (chart C ⟨1⟩)).inv).val.app (.op ⊤)).hom
          (1 : Γ(affine C, ⊤)))) = _
  rw [hu, monomial_right_value]
  exact (show (Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ (d - d)) =
    (1 : Γ(affine C, ⊤)) by simp).trans
      (unitIso_inv_hom_top (Scheme.Modules.restrictUnitIso (chart C ⟨1⟩))).symm


private theorem polynomial_charts_iSup (C : Type u) [CommRing C] :
    (⨆ j : ULift.{u} (Fin 2), (chart C j).opensRange) = ⊤ := by
  have he := Proj.iSup_basicOpen_eq_top
    (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) C)
    (MvPolynomial.X : ULift.{u} (Fin 2) → MvPolynomial (ULift.{u} (Fin 2)) C)
    (projective_irrelevant_eq_span C (ULift.{u} (Fin 2))).le
  apply le_antisymm le_top
  intro x hx
  have hx' : x ∈ ⨆ j : ULift.{u} (Fin 2),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) C)
        (MvPolynomial.X j) := by rw [he]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨j, ?_⟩
  change x ∈ Set.range (chart C j)
  rwa [← projectiveLinePolynomialChart_range] at hj

private theorem mapped_section_epi {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {U A B : D} {i : U ⟶ A} {φ : A ⟶ B} {s : U ⟶ B}
    (hi : i ≫ φ = s) {V : E} {t : F.obj B ⟶ V} {v : F.obj U ⟶ V}
    (hs : F.map s ≫ t = v) [IsIso t] [IsIso v] : Epi (F.map φ) := by
  have he : F.map s = v ≫ inv t := by
    calc
      F.map s = (F.map s ≫ t) ≫ inv t := by simp
      _ = v ≫ inv t := by rw [hs]
  let : Epi (F.map s) := he.symm ▸ inferInstance
  have hm : F.map i ≫ F.map φ = F.map s :=
    (F.map_comp i φ).symm.trans (congrArg F.map hi)
  let : Epi (F.map i ≫ F.map φ) := hm.symm ▸ inferInstance
  exact epi_of_epi (F.map i) (F.map φ)

private theorem ordinaryEval_left_epi (C : Type u) [CommRing C] (d : ℕ) :
    Epi ((Scheme.Modules.restrictFunctor (chart C ⟨0⟩)).map
      (projectiveOrdinaryEval C d)) := by
  let : IsIso (SchubertGeometry.ProjectiveLine.projectiveTransitionChart C d ⟨0⟩).hom :=
    (SchubertGeometry.ProjectiveLine.projectiveTransitionChart C d ⟨0⟩).isIso_hom
  let : IsIso (Scheme.Modules.restrictUnitIso (chart C ⟨0⟩)).hom :=
    (Scheme.Modules.restrictUnitIso (chart C ⟨0⟩)).isIso_hom
  exact mapped_section_epi
    (Scheme.Modules.restrictFunctor (chart C ⟨0⟩))
    (ordinaryEval_inl C d) (leftEndpoint C d)

private theorem ordinaryEval_right_epi (C : Type u) [CommRing C] (d : ℕ) :
    Epi ((Scheme.Modules.restrictFunctor (chart C ⟨1⟩)).map
      (projectiveOrdinaryEval C d)) := by
  let : IsIso (SchubertGeometry.ProjectiveLine.projectiveTransitionChart C d ⟨1⟩).hom :=
    (SchubertGeometry.ProjectiveLine.projectiveTransitionChart C d ⟨1⟩).isIso_hom
  let : IsIso (Scheme.Modules.restrictUnitIso (chart C ⟨1⟩)).hom :=
    (Scheme.Modules.restrictUnitIso (chart C ⟨1⟩)).isIso_hom
  exact mapped_section_epi
    (Scheme.Modules.restrictFunctor (chart C ⟨1⟩))
    (ordinaryEval_inr C d) (rightEndpoint C d)

private theorem uliftFinTwo_forall (P : ULift.{u} (Fin 2) → Prop)
    (h0 : P ⟨0⟩) (h1 : P ⟨1⟩) : ∀ j, P j := by
  rintro ⟨j⟩
  fin_cases j
  · exact h0
  · exact h1

private theorem ordinaryEval_chart_epi (C : Type u) [CommRing C] (d : ℕ) :
    ∀ j : ULift.{u} (Fin 2), Epi ((Scheme.Modules.restrictFunctor (chart C j)).map
      (projectiveOrdinaryEval C d)) :=
  uliftFinTwo_forall
    (fun j => Epi ((Scheme.Modules.restrictFunctor (chart C j)).map
      (projectiveOrdinaryEval C d)))
    (ordinaryEval_left_epi C d) (ordinaryEval_right_epi C d)

/-- The endpoint monomials generate the transition module on the two standard charts. -/
theorem projectiveOrdinaryEval_epi (C : Type u) [CommRing C] (d : ℕ) :
    Epi (projectiveOrdinaryEval C d) :=
  module_epi_cover (X := line C) (I := ULift.{u} (Fin 2))
    (Y := fun _ => affine C) (chart C) (polynomial_charts_iSup C)
    (M := structureModule (line C) ⨿ structureModule (line C))
    (N := SchubertGeometry.ProjectiveLine.projectiveTransitionModule C d)
    (projectiveOrdinaryEval C d) (ordinaryEval_chart_epi C d)

end SchubertGeometry.ProjectiveLine
