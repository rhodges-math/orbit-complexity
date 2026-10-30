import OrbitComplexity.FrobeniusSplitting.Cartier.PolynomialTrace

/-! # Trace-dual weights for the Frobenius residue coordinates -/

open Polynomial
noncomputable section

namespace FrobeniusSplitting

variable (C : Type*) [CommRing C] (p : ℕ) [ExpChar C p] [PerfectRing C p]

private def residueCoordinate (i : Fin p) : FrobeniusLinearMap (Polynomial C) p := by
  let domain := (inferInstance : Module (Polynomial C) (Fin p → Polynomial C))
  letI := polynomialAbsoluteModule C p
  letI := domain
  let e := polynomialAbsoluteEval C p
  refine
    { toAddMonoidHom :=
        { toFun := fun f => (e.symm f) i
          map_zero' := congrFun e.symm.map_zero i
          map_add' := fun f g => congrFun (e.symm.map_add f g) i }
      map_pow_mul' := ?_ }
  intro a b
  have h : e.symm (a ^ p * b) = a • e.symm b := e.symm.map_smul a b
  exact congrFun h i

private theorem residueCoordinate_monomial (i j : Fin p) :
    residueCoordinate C p i (X ^ (j : ℕ)) = if i = j then 1 else 0 := by
  classical
  have he : polynomialAbsoluteEval C p (Pi.single j (1 : Polynomial C)) =
      X ^ (j : ℕ) := by
    rw [polynomialAbsoluteEval_apply]
    simp [Pi.single_apply, expChar_ne_zero C p]
  change ((polynomialAbsoluteEval C p).symm (X ^ (j : ℕ))) i = _
  rw [← he, LinearEquiv.symm_apply_apply]
  simp [Pi.single_apply]

/-- The coordinate operators of the residue basis are weighted canonical traces. -/
theorem exists_polynomialTrace_dual :
    ∃ w : Fin p → Polynomial C, ∀ i j : Fin p,
      univariateTrace (RingSplitting.ofPerfectRing C p) (w i * X ^ (j : ℕ)) =
        if i = j then 1 else 0 := by
  classical
  choose w hw using fun i : Fin p =>
    polynomialTrace_weight_surjective C p (residueCoordinate C p i)
  refine ⟨w, ?_⟩
  intro i j
  have h := congrArg
    (fun φ : FrobeniusLinearMap (Polynomial C) p => φ (X ^ (j : ℕ))) (hw i)
  exact h.trans (residueCoordinate_monomial C p i j)

end FrobeniusSplitting
