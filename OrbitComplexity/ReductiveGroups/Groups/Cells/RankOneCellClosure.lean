import OrbitComplexity.ReductiveGroups.Groups.Cells.PointFlagSpace
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductCoordinates
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Rank One Cell Closure

Rank-one closure: if every nonzero point `y(d)` of a Ga morphism
lies in a double coset `B n B`, then the identity lies in the Zariski closure
of `B n B` in the `K`-points. (In the flag space this is `B ⊆ closure(B s B)`.) -/

noncomputable section
namespace ReductiveGroups

open TauCeti MvPolynomial

universe u
variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]

/-- The double coset `H n H` of a subgroup of points. -/
def pointDoubleCoset (H : Subgroup (WithConv (B →ₐ[K] K))) (n : WithConv (B →ₐ[K] K)) :
    Set (WithConv (B →ₐ[K] K)) :=
  {g | ∃ h₁ ∈ H, ∃ h₂ ∈ H, g = h₁ * n * h₂}

omit [HopfAlgebra K B] in
private theorem MvPolynomial.unit_eq_zero_of_eval_ne_zero [Infinite K]
    (p : MvPolynomial Unit K) (hp : ∀ d : K, d ≠ 0 → eval (fun _ => d) p = 0) : p = 0 := by
  have hq : X () * p = 0 := by
    apply MvPolynomial.funext
    intro v
    by_cases hv : v () = 0
    · simp [hv]
    · have hvfun : v = fun _ => v () := funext fun u => by cases u; rfl
      rw [map_mul, eval_X, map_zero, hvfun, hp (v ()) hv, mul_zero]
  exact (mul_eq_zero.mp hq).resolve_left (X_ne_zero ())

/-- **Rank-one closure.** If `y(d) ∈ H n H` for every `d ≠ 0`, then the
identity lies in the Zariski closure of `H n H`. -/
theorem one_mem_closure_pointDoubleCoset [Infinite K]
    (H : Subgroup (WithConv (B →ₐ[K] K))) (n : WithConv (B →ₐ[K] K))
    (y : B →ₐc[K] SymmetricAlgebra K K)
    (hy : ∀ d : K, d ≠ 0 → gaParameterPoint y d ∈ pointDoubleCoset H n) :
    (1 : WithConv (B →ₐ[K] K)) ∈ closure (pointDoubleCoset H n) := by
  obtain ⟨S, hS⟩ := (pointGroup_isClosed_iff _).mp (isClosed_closure (s := pointDoubleCoset H n))
  rw [hS]
  intro f hf
  let P : B →ₐ[K] MvPolynomial Unit K := gaProductCoordinate (fun _ : Unit => y) [()]
  have hPeval (d : K) : eval (fun _ => d) (P f) = (gaParameterPoint y d).ofConv f := by
    have h := congrArg (fun φ : B →ₐ[K] K => φ f)
      (gaProductCoordinate_eval (fun _ : Unit => y) [()] (fun _ => d))
    simpa [P] using h
  have hzero : P f = 0 := by
    apply MvPolynomial.unit_eq_zero_of_eval_ne_zero
    intro d hd
    rw [hPeval]
    have hmem : gaParameterPoint y d ∈ closure (pointDoubleCoset H n) :=
      subset_closure (hy d hd)
    rw [hS] at hmem
    exact hmem f hf
  have h0 := hPeval 0
  rw [hzero, map_zero] at h0
  have hone : gaParameterPoint y (0 : K) = 1 := by
    simp only [gaParameterPoint, ofAdd_zero, map_one]
  rw [hone] at h0
  exact h0.symm

end ReductiveGroups
