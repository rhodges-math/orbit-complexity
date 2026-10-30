import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.InfinityFactor
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.FrobeniusGenerators
import Mathlib.Data.Fin.Rev

/-! # Monomial generators after multiplying by the infinity factor -/

open AlgebraicGeometry CategoryTheory Opposite GroupActions FrobeniusSplitting
open SchubertGeometry.ProjectiveLine
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveLine

private theorem unit_smul_top {X : Scheme.{u}} (r s : Γ(X, ⊤)) :
    ((Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r).val.app
      (.op ⊤)).hom s = r * s := by
  change X.presheaf.map (𝟙 (.op ⊤)) r * s = r * s
  simp

private theorem infinity_zero_value (C : Type u) [CommRing C] (d : ℕ)
    (s : (projectiveTransitionModule C d).val.obj
      (.op (projectiveLinePolynomialChart C ⟨0⟩ ''ᵁ ⊤))) :
    ((leftChartMap C (2 * d)).val.app (.op ⊤)).hom
      (((projectiveInfinityFactor C d).val.app
        (.op (projectiveLinePolynomialChart C ⟨0⟩ ''ᵁ ⊤))).hom s) =
      ((leftChartMap C d).val.app (.op ⊤)).hom s :=
  congrArg (fun f => (f.val.app (.op ⊤)).hom s)
    (projectiveInfinityFactor_charts C d).1

private theorem infinity_one_value (C : Type u) [CommRing C] (d : ℕ)
    (s : (projectiveTransitionModule C d).val.obj
      (.op (projectiveLinePolynomialChart C ⟨1⟩ ''ᵁ ⊤))) :
    (show Γ(Spec (.of (Polynomial C)), ⊤) from
      ((rightChartMap C (2 * d)).val.app (.op ⊤)).hom
      (((projectiveInfinityFactor C d).val.app
        (.op (projectiveLinePolynomialChart C ⟨1⟩ ''ᵁ ⊤))).hom s)) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ d) *
        (show Γ(Spec (.of (Polynomial C)), ⊤) from
          ((rightChartMap C d).val.app (.op ⊤)).hom s) := by
  exact (congrArg (fun f => (f.val.app (.op ⊤)).hom s)
    (projectiveInfinityFactor_charts C d).2).trans (unit_smul_top _ _)

/-- Reversing the residue basis and multiplying by the infinity factor gives
the pair of monomials X^(p-1-k) and Y^(p-1+k). -/
theorem projectiveInfinityFactor_generators (C : Type u) [CommRing C]
    (p : ℕ) [ExpChar C p] (k : ULift.{u} (Fin p)) :
    let s := SheafOfModules.freeHomEquiv
      (frobeniusRestriction C p (projectiveToSpec C (ULift.{u} (Fin 2)))
        (projectiveTransitionModule C (p - 1))) (projectiveFrobeniusEval C p)
          (ULift.up k.down.rev)
    (((leftChartMap C (2 * (p - 1))).val.app (.op ⊤)).hom
      (((projectiveInfinityFactor C (p - 1)).val.app
        (.op (projectiveLinePolynomialChart C ⟨0⟩ ''ᵁ ⊤))).hom
        (s.val (.op (projectiveLinePolynomialChart C ⟨0⟩ ''ᵁ ⊤)))) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv
        (Polynomial.X ^ (p - 1 - (k.down : ℕ)))) ∧
    (((rightChartMap C (2 * (p - 1))).val.app (.op ⊤)).hom
      (((projectiveInfinityFactor C (p - 1)).val.app
        (.op (projectiveLinePolynomialChart C ⟨1⟩ ''ᵁ ⊤))).hom
        (s.val (.op (projectiveLinePolynomialChart C ⟨1⟩ ''ᵁ ⊤)))) =
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv
        (Polynomial.X ^ (p - 1 + (k.down : ℕ)))) := by
  let i : ULift.{u} (Fin p) := ⟨k.down.rev⟩
  let s := SheafOfModules.freeHomEquiv
    (frobeniusRestriction C p (projectiveToSpec C (ULift.{u} (Fin 2)))
      (projectiveTransitionModule C (p - 1))) (projectiveFrobeniusEval C p) i
  have hzero : ((leftChartMap C (p - 1)).val.app (.op ⊤)).hom
      (s.val (.op (projectiveLinePolynomialChart C ⟨0⟩ ''ᵁ ⊤))) =
        (Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ (i.down : ℕ)) :=
    (projectiveEval_generators C p i).1
  have hone : ((rightChartMap C (p - 1)).val.app (.op ⊤)).hom
      (s.val (.op (projectiveLinePolynomialChart C ⟨1⟩ ''ᵁ ⊤))) =
        (Scheme.ΓSpecIso (.of (Polynomial C))).inv
          (Polynomial.X ^ (p - 1 - (i.down : ℕ))) :=
    (projectiveEval_generators C p i).2
  have hi : (i.down : ℕ) = p - 1 - (k.down : ℕ) := by
    simp only [i, Fin.val_rev]
    omega
  have hrev : p - 1 - (i.down : ℕ) = (k.down : ℕ) := by
    rw [hi]
    have hk := k.down.isLt
    omega
  constructor
  · exact (infinity_zero_value C (p - 1) _).trans (hzero.trans (by rw [hi]))
  · refine (infinity_one_value C (p - 1)
      (s.val (.op (projectiveLinePolynomialChart C ⟨1⟩ ''ᵁ ⊤)))).trans ?_
    refine (congrArg (fun t : Γ(Spec (.of (Polynomial C)), ⊤) =>
      (Scheme.ΓSpecIso (.of (Polynomial C))).inv (Polynomial.X ^ (p - 1)) * t) hone).trans ?_
    rw [hrev]
    exact (map_mul (Scheme.ΓSpecIso (.of (Polynomial C))).inv.hom _ _).symm.trans
      (congrArg ((Scheme.ΓSpecIso (.of (Polynomial C))).inv)
        (pow_add Polynomial.X (p - 1) (k.down : ℕ)).symm)

end SchubertGeometry.ProjectiveLine
