import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.FrobeniusGenerators
import OrbitComplexity.FrobeniusSplitting.Modules.Sections
import OrbitComplexity.FrobeniusSplitting.Modules.Frobenius
import OrbitComplexity.FrobeniusSplitting.Modules.Polynomial
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Topology.Sheaves.Stalks

/-! # Local evaluation in the coherent projective transition module -/

open AlgebraicGeometry CategoryTheory GroupActions FrobeniusSplitting
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

private def sourceModule (C : Type u) [CommRing C] (p : ℕ) :
    (projectiveScheme C (ULift.{u} (Fin 2))).Modules :=
  SheafOfModules.free (R := (projectiveScheme C (ULift.{u} (Fin 2))).ringCatSheaf)
    (ULift.{u} (Fin p))

private def sourceChart (C : Type u) [CommRing C] (p : ℕ) (j : ULift.{u} (Fin 2)) :
    (Spec (.of (Polynomial C))).Modules :=
  (sourceModule C p).restrict (projectiveLinePolynomialChart C j)

private def powerFunctor (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) : X.Modules ⥤ X.Modules :=
  SheafOfModules.pushforward (F := 𝟭 X.Opens) (sheafFrobenius C p base)

private def targetChart (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    (j : ULift.{u} (Fin 2)) :
    (frobeniusRestriction C p (projectiveToSpec C (ULift.{u} (Fin 2)))
      (projectiveTransitionModule C (p - 1))).restrict
        (projectiveLinePolynomialChart C j) ≅
      frobeniusRestriction C p
        (projectiveLinePolynomialChart C j ≫ projectiveToSpec C (ULift.{u} (Fin 2)))
        (SheafOfModules.unit (Spec (.of (Polynomial C))).ringCatSheaf) :=
  frobeniusRestrictIso C p (projectiveToSpec C (ULift.{u} (Fin 2)))
      (projectiveLinePolynomialChart C j) (projectiveTransitionModule C (p - 1)) ≪≫
    (powerFunctor C p
      (projectiveLinePolynomialChart C j ≫ projectiveToSpec C (ULift.{u} (Fin 2)))).mapIso
        (projectiveTransitionChart C (p - 1) j)

private def evaluationChart (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    (j : ULift.{u} (Fin 2)) :
    sourceChart C p j ⟶
      frobeniusRestriction C p
        (projectiveLinePolynomialChart C j ≫ projectiveToSpec C (ULift.{u} (Fin 2)))
        (SheafOfModules.unit (Spec (.of (Polynomial C))).ringCatSheaf) :=
  (Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart C j)).map
    (projectiveFrobeniusEval C p) ≫ (targetChart C p j).hom

private instance sourceModule_qc (C : Type u) [CommRing C] (p : ℕ) :
    (sourceModule C p).IsQuasicoherent := by
  dsimp only [sourceModule]
  infer_instance

private instance sourceChart_qc (C : Type u) [CommRing C] (p : ℕ)
    (j : ULift.{u} (Fin 2)) : (sourceChart C p j).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_restrictFunctor
    (projectiveLinePolynomialChart C j) (sourceModule C p)

private instance chartTarget_qc (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    (j : ULift.{u} (Fin 2)) :
    (frobeniusRestriction C p
      (projectiveLinePolynomialChart C j ≫ projectiveToSpec C (ULift.{u} (Fin 2)))
      (SheafOfModules.unit (Spec (.of (Polynomial C))).ringCatSheaf)).IsQuasicoherent := by
  let M : (Spec (.of (Polynomial C))).Modules :=
    SheafOfModules.unit (Spec (.of (Polynomial C))).ringCatSheaf
  let : M.IsQuasicoherent := (isQuasicoherent_iff_isIso_fromTildeΓ M).mpr inferInstance
  exact frobeniusAffine_isQuasicoherent C p
    (projectiveLinePolynomialChart C j ≫ projectiveToSpec C (ULift.{u} (Fin 2))) M

private theorem evaluationChart_isIso_of_top (C : Type u) [CommRing C]
    (p : ℕ) [ExpChar C p] (j : ULift.{u} (Fin 2))
    (h : Function.Bijective ((moduleSpecΓFunctor.map (evaluationChart C p j)).hom)) :
    IsIso (evaluationChart C p j) :=
  affineModule_isIso _ h

private def sourceGenerator (C : Type u) [CommRing C] (p : ℕ)
    (j : ULift.{u} (Fin 2)) (k : ULift.{u} (Fin p)) :
    moduleSpecΓFunctor.obj (sourceChart C p j) :=
  ((SheafOfModules.ιFree
      (R := (projectiveScheme C (ULift.{u} (Fin 2))).ringCatSheaf) k).val.app
        (.op (projectiveLinePolynomialChart C j ''ᵁ ⊤))).hom
    (1 : Γ(projectiveScheme C (ULift.{u} (Fin 2)),
      projectiveLinePolynomialChart C j ''ᵁ ⊤))

private theorem evaluation_generator_zero (C : Type u) [CommRing C]
    (p : ℕ) [ExpChar C p] (k : ULift.{u} (Fin p)) :
    (moduleSpecΓFunctor.map (evaluationChart C p ⟨0⟩)).hom
      (sourceGenerator C p ⟨0⟩ k) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ (k.down : ℕ)) := by
  change (((projectiveTransitionChart C (p - 1) ⟨0⟩).hom.val.app (.op ⊤)).hom
    ((SheafOfModules.freeHomEquiv
      (frobeniusRestriction C p (projectiveToSpec C (ULift.{u} (Fin 2)))
        (projectiveTransitionModule C (p - 1)))
      (projectiveFrobeniusEval C p) k).val
        (.op (projectiveLinePolynomialChart C ⟨0⟩ ''ᵁ ⊤)))) = _
  exact (projectiveEval_generators C p k).1

private theorem evaluation_generator_one (C : Type u) [CommRing C]
    (p : ℕ) [ExpChar C p] (k : ULift.{u} (Fin p)) :
    (moduleSpecΓFunctor.map (evaluationChart C p ⟨1⟩)).hom
      (sourceGenerator C p ⟨1⟩ k) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv
        (Polynomial.X ^ (p - 1 - (k.down : ℕ))) := by
  change (((projectiveTransitionChart C (p - 1) ⟨1⟩).hom.val.app (.op ⊤)).hom
    ((SheafOfModules.freeHomEquiv
      (frobeniusRestriction C p (projectiveToSpec C (ULift.{u} (Fin 2)))
        (projectiveTransitionModule C (p - 1)))
      (projectiveFrobeniusEval C p) k).val
        (.op (projectiveLinePolynomialChart C ⟨1⟩ ''ᵁ ⊤)))) = _
  exact (projectiveEval_generators C p k).2

private def coefficientChart (C : Type u) [CommRing C] (j : ULift.{u} (Fin 2)) :
    Γ(projectiveScheme C (ULift.{u} (Fin 2)),
      projectiveLinePolynomialChart C j ''ᵁ ⊤) ≃+* Polynomial C :=
  (((projectiveLinePolynomialChart C j).appIso ⊤) ≪≫
    Scheme.ΓSpecIso (.of (Polynomial C))).commRingCatIsoToRingEquiv

private def sourceCoordinates (C : Type u) [CommRing C] (p : ℕ)
    (j : ULift.{u} (Fin 2)) (v : Fin p → Polynomial C) :
    moduleSpecΓFunctor.obj (sourceChart C p j) :=
  (finiteFreeSectionsIso (projectiveScheme C (ULift.{u} (Fin 2)))
    (projectiveLinePolynomialChart C j ''ᵁ ⊤) (ULift.{u} (Fin p))).hom.hom
    (Finsupp.equivFunOnFinite.symm
      (fun k : ULift.{u} (Fin p) => (coefficientChart C j).symm (v k.down)))

private theorem sourceCoordinates_bijective (C : Type u) [CommRing C]
    (p : ℕ) (j : ULift.{u} (Fin 2)) : Function.Bijective (sourceCoordinates C p j) := by
  have hu : Function.Bijective
      (fun v : Fin p → Polynomial C => fun k : ULift.{u} (Fin p) => v k.down) := by
    constructor
    · intro v w h
      funext i
      exact congrFun h ⟨i⟩
    · intro v
      refine ⟨(fun i => v ⟨i⟩), ?_⟩
      funext k
      cases k
      rfl
  have hc := (Equiv.piCongrRight
    (fun _ : ULift.{u} (Fin p) => (coefficientChart C j).symm.toEquiv)).bijective
  have hf := (Finsupp.equivFunOnFinite
    (α := ULift.{u} (Fin p))
    (M := Γ(projectiveScheme C (ULift.{u} (Fin 2)),
      projectiveLinePolynomialChart C j ''ᵁ ⊤))).symm.bijective
  have he := (finiteFreeSectionsIso (projectiveScheme C (ULift.{u} (Fin 2)))
    (projectiveLinePolynomialChart C j ''ᵁ ⊤) (ULift.{u} (Fin p))).toLinearEquiv.bijective
  exact he.comp (hf.comp (hc.comp hu))

private theorem source_smul (C : Type u) [CommRing C] (p : ℕ)
    (j : ULift.{u} (Fin 2)) (r : Polynomial C)
    (s : moduleSpecΓFunctor.obj (sourceChart C p j)) :
    r • s = ((sourceModule C p).smul ((coefficientChart C j).symm r)).hom
      (show Γ(sourceModule C p, projectiveLinePolynomialChart C j ''ᵁ ⊤) from s) := by
  erw [Scheme.Modules.smul_Spec_def]
  rfl

private theorem target_smul (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    (j : ULift.{u} (Fin 2)) (r : Polynomial C)
    (s : moduleSpecΓFunctor.obj
      (frobeniusRestriction C p
        (projectiveLinePolynomialChart C j ≫ projectiveToSpec C (ULift.{u} (Fin 2)))
        (SheafOfModules.unit (Spec (.of (Polynomial C))).ringCatSheaf))) :
    r • s = ((Scheme.ΓSpecIso (.of (Polynomial C))).inv r) ^ p *
      (show Γ(Spec (.of (Polynomial C)), ⊤) from s) := by
  erw [Scheme.Modules.smul_Spec_def]
  rfl

private def sourceSum (C : Type u) [CommRing C] (p : ℕ)
    (j : ULift.{u} (Fin 2)) (v : Fin p → Polynomial C) :
    moduleSpecΓFunctor.obj (sourceChart C p j) :=
  ∑ k : ULift.{u} (Fin p), v k.down • sourceGenerator C p j k

private theorem sourceCoordinates_eq (C : Type u) [CommRing C] (p : ℕ)
    (j : ULift.{u} (Fin 2)) (v : Fin p → Polynomial C) :
    sourceCoordinates C p j v = sourceSum C p j v := by
  have hf : Finsupp.equivFunOnFinite.symm
      (fun k : ULift.{u} (Fin p) => (coefficientChart C j).symm (v k.down)) =
      ∑ k : ULift.{u} (Fin p), Finsupp.single k ((coefficientChart C j).symm (v k.down)) := by
    exact Finsupp.equivFunOnFinite_symm_eq_sum _
  unfold sourceCoordinates sourceSum
  rw [hf, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  erw [finiteFreeSectionsIso_single, source_smul]
  change ((SheafOfModules.ιFree
    (R := (projectiveScheme C (ULift.{u} (Fin 2))).ringCatSheaf) k).val.app
      (.op (projectiveLinePolynomialChart C j ''ᵁ ⊤))).hom
    ((coefficientChart C j).symm (v k.down)) = _
  have h := (((SheafOfModules.ιFree
      (R := (projectiveScheme C (ULift.{u} (Fin 2))).ringCatSheaf) k).val.app
        (.op (projectiveLinePolynomialChart C j ''ᵁ ⊤))).hom.map_smul
      ((coefficientChart C j).symm (v k.down))
      (1 : Γ(projectiveScheme C (ULift.{u} (Fin 2)),
        projectiveLinePolynomialChart C j ''ᵁ ⊤)))
  change ((SheafOfModules.ιFree
    (R := (projectiveScheme C (ULift.{u} (Fin 2))).ringCatSheaf) k).val.app
      (.op (projectiveLinePolynomialChart C j ''ᵁ ⊤))).hom
    (show Γ(projectiveScheme C (ULift.{u} (Fin 2)),
      projectiveLinePolynomialChart C j ''ᵁ ⊤) from
        (coefficientChart C j).symm (v k.down) * 1) =
    ((sourceModule C p).smul ((coefficientChart C j).symm (v k.down))).hom
      (sourceGenerator C p j k) at h
  simpa only [mul_one] using h

private theorem evaluation_zero (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    (v : Fin p → Polynomial C) :
    (Scheme.ΓSpecIso (.of (Polynomial C))).hom
      ((moduleSpecΓFunctor.map (evaluationChart C p ⟨0⟩)).hom
        (sourceCoordinates C p ⟨0⟩ v)) =
      ∑ k : Fin p, (v k) ^ p * Polynomial.X ^ (k : ℕ) := by
  rw [sourceCoordinates_eq]
  unfold sourceSum
  erw [map_sum, map_sum]
  calc
    _ = ∑ k : ULift.{u} (Fin p), (v k.down) ^ p * Polynomial.X ^ (k.down : ℕ) := by
      apply Finset.sum_congr rfl
      intro k hk
      erw [map_smul, evaluation_generator_zero, target_smul]
      simp only [map_mul, map_pow, Iso.inv_hom_id_apply]
    _ = _ := Fintype.sum_equiv Equiv.ulift _ _ (fun _ => rfl)

private theorem evaluation_one (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    (v : Fin p → Polynomial C) :
    (Scheme.ΓSpecIso (.of (Polynomial C))).hom
      ((moduleSpecΓFunctor.map (evaluationChart C p ⟨1⟩)).hom
        (sourceCoordinates C p ⟨1⟩ v)) =
      ∑ k : Fin p, (v k) ^ p * Polynomial.X ^ (p - 1 - (k : ℕ)) := by
  rw [sourceCoordinates_eq]
  unfold sourceSum
  erw [map_sum, map_sum]
  calc
    _ = ∑ k : ULift.{u} (Fin p),
        (v k.down) ^ p * Polynomial.X ^ (p - 1 - (k.down : ℕ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      erw [map_smul, evaluation_generator_one, target_smul]
      simp only [map_mul, map_pow, Iso.inv_hom_id_apply]
    _ = _ := Fintype.sum_equiv Equiv.ulift _ _ (fun _ => rfl)

private def outputCoefficients (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    (j : ULift.{u} (Fin 2))
    (s : moduleSpecΓFunctor.obj
      (frobeniusRestriction C p
        (projectiveLinePolynomialChart C j ≫ projectiveToSpec C (ULift.{u} (Fin 2)))
        (SheafOfModules.unit (Spec (.of (Polynomial C))).ringCatSheaf))) : Polynomial C :=
  (Scheme.ΓSpecIso (.of (Polynomial C))).hom
    (show Γ(Spec (.of (Polynomial C)), ⊤) from s)

private theorem evaluationChart_isIso_of_coordinates (C : Type u) [CommRing C]
    (p : ℕ) [ExpChar C p] (j : ULift.{u} (Fin 2))
    (h : Function.Bijective (fun v : Fin p → Polynomial C =>
      outputCoefficients C p j ((moduleSpecΓFunctor.map (evaluationChart C p j)).hom
        (sourceCoordinates C p j v)))) : IsIso (evaluationChart C p j) := by
  apply evaluationChart_isIso_of_top
  have hf : Function.Bijective (fun s => outputCoefficients C p j
      ((moduleSpecΓFunctor.map (evaluationChart C p j)).hom s)) :=
    (Function.Bijective.of_comp_iff _ (sourceCoordinates_bijective C p j)).mp h
  have he : Function.Bijective (outputCoefficients C p j) :=
    (Scheme.ΓSpecIso (.of (Polynomial C))).commRingCatIsoToRingEquiv.bijective
  exact (Function.Bijective.of_comp_iff' he _).mp hf

private theorem evaluationChart_zero_isIso (C : Type u) [CommRing C] (p : ℕ)
    [ExpChar C p] [PerfectRing C p] : IsIso (evaluationChart C p ⟨0⟩) := by
  apply evaluationChart_isIso_of_coordinates
  have h : (fun v : Fin p → Polynomial C =>
      outputCoefficients C p ⟨0⟩ ((moduleSpecΓFunctor.map (evaluationChart C p ⟨0⟩)).hom
        (sourceCoordinates C p ⟨0⟩ v))) = fun v => polynomialAbsoluteEval C p v := by
    funext v
    exact (evaluation_zero C p v).trans (polynomialAbsoluteEval_apply C p v).symm
  rw [h]
  exact (polynomialAbsoluteEval C p).bijective

private theorem reverse_eval (C : Type u) [CommRing C] (p : ℕ)
    (v : Fin p → Polynomial C) :
    (∑ k : Fin p, (v k) ^ p * Polynomial.X ^ (p - 1 - (k : ℕ))) =
      ∑ k : Fin p, (v k.rev) ^ p * Polynomial.X ^ (k : ℕ) := by
  apply Fintype.sum_equiv Fin.revPerm
  intro k
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  congr 2
  change p - 1 - (k : ℕ) = p - ((k : ℕ) + 1)
  omega

private theorem reverse_bijective (C : Type u) [CommRing C] (p : ℕ) :
    Function.Bijective (fun v : Fin p → Polynomial C => fun k : Fin p => v k.rev) := by
  constructor
  · intro v w h
    funext k
    simpa only [Fin.rev_rev] using congrFun h k.rev
  · intro v
    refine ⟨fun k : Fin p => v k.rev, ?_⟩
    funext k
    exact congrArg v (Fin.rev_rev k)

private theorem evaluationChart_one_isIso (C : Type u) [CommRing C] (p : ℕ)
    [ExpChar C p] [PerfectRing C p] : IsIso (evaluationChart C p ⟨1⟩) := by
  apply evaluationChart_isIso_of_coordinates
  have h : (fun v : Fin p → Polynomial C =>
      outputCoefficients C p ⟨1⟩ ((moduleSpecΓFunctor.map (evaluationChart C p ⟨1⟩)).hom
        (sourceCoordinates C p ⟨1⟩ v))) =
      fun v => polynomialAbsoluteEval C p (fun k => v k.rev) := by
    funext v
    exact (evaluation_one C p v).trans
      ((reverse_eval C p v).trans (polynomialAbsoluteEval_apply C p _).symm)
  rw [h]
  exact (polynomialAbsoluteEval C p).bijective.comp (reverse_bijective C p)

private theorem polynomial_charts_cover (C : Type u) [CommRing C]
    (x : projectiveScheme C (ULift.{u} (Fin 2))) :
    ∃ (j : ULift.{u} (Fin 2)) (y : Spec (.of (Polynomial C))),
      projectiveLinePolynomialChart C j y = x := by
  have he := Proj.iSup_basicOpen_eq_top
    (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) C)
    (MvPolynomial.X : ULift.{u} (Fin 2) → MvPolynomial (ULift.{u} (Fin 2)) C)
    (projective_irrelevant_eq_span C (ULift.{u} (Fin 2))).le
  have hx : x ∈ ⨆ j : ULift.{u} (Fin 2),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) C)
        (MvPolynomial.X j) := by
    rw [he]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  rw [← projectiveLinePolynomialChart_range] at hj
  obtain ⟨y, hy⟩ := hj
  exact ⟨j, y, hy⟩

/-- Over perfect coefficients, the global rank-p Frobenius evaluation is
an isomorphism of module sheaves. -/
theorem projectiveFrobeniusEval_isIso (C : Type u) [CommRing C] (p : ℕ)
    [ExpChar C p] [PerfectRing C p] : IsIso (projectiveFrobeniusEval C p) := by
  apply isIso_on_open_family (fun _ : ULift.{u} (Fin 2) => Spec (.of (Polynomial C)))
    (projectiveLinePolynomialChart C) (polynomial_charts_cover C)
  intro j
  have hi : IsIso (evaluationChart C p j) := by
    rcases j with ⟨j⟩
    fin_cases j
    · exact evaluationChart_zero_isIso C p
    · exact evaluationChart_one_isIso C p
  let : IsIso ((Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart C j)).map
      (projectiveFrobeniusEval C p) ≫ (targetChart C p j).hom) := hi
  exact IsIso.of_isIso_comp_right
    ((Scheme.Modules.restrictFunctor (projectiveLinePolynomialChart C j)).map
      (projectiveFrobeniusEval C p)) (targetChart C p j).hom

end SchubertGeometry.ProjectiveLine
