import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupConjugation
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Equality of additive subgroup images on a tangent line

Proportional nonzero tangents give the same additive subgroup, with the scalar change
of parameter dictated by the tangent equation.
-/

namespace ReductiveGroups
noncomputable section
open TauCeti
universe u
variable {K B : Type u} [Field K] [CharZero K] [CommRing B]
  [HopfAlgebra K B] [Algebra.FiniteType K B]

/-- Proportional Ga tangents give the corresponding scalar reparametrization on points. -/
private theorem gaParameterPoint_of_tangent_smul
    (x y : B →ₐc[K] SymmetricAlgebra K K) (c : K)
    (h : gaAffineGroupTangent x = c • gaAffineGroupTangent y) (t : K) :
    gaParameterPoint x t = gaParameterPoint y (c * t) := by
  change gaAffineGroupPoints x (Multiplicative.ofAdd t) =
    gaAffineGroupPoints y (Multiplicative.ofAdd (c * t))
  have he := GaAffineGroupPoints.conjugate_of_tangent_eq x y 1 c
    (by simpa only [map_one, Module.End.one_apply] using h) t
  simpa only [one_mul, inv_one, mul_one] using he

/-- A nonzero scalar tangent comparison identifies the full Ga point images. -/
private theorem gaParameterPoint_range_of_smul
    (x y : B →ₐc[K] SymmetricAlgebra K K) (c : K) (hc : c ≠ 0)
    (h : gaAffineGroupTangent x = c • gaAffineGroupTangent y) :
    Set.range (fun t : K => gaParameterPoint x t) =
      Set.range (fun t : K => gaParameterPoint y t) := by
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨c * t, (gaParameterPoint_of_tangent_smul x y c h t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨c⁻¹ * t, ?_⟩
    change gaParameterPoint x (c⁻¹ * t) = gaParameterPoint y t
    rw [gaParameterPoint_of_tangent_smul x y c h, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- Nonzero vectors in the same one-dimensional tangent submodule give the same Ga image. -/
theorem gaParameterPoint_range_of_line
    (W : Submodule K (Derivation K B (Bialgebra.CounitAlgebra K B K)))
    (hW : Module.finrank K W = 1)
    (x y : B →ₐc[K] SymmetricAlgebra K K)
    (hx : gaAffineGroupTangent x ∈ W) (hy : gaAffineGroupTangent y ∈ W)
    (hx0 : gaAffineGroupTangent x ≠ 0) (hy0 : gaAffineGroupTangent y ≠ 0) :
    Set.range (fun t : K => gaParameterPoint x t) =
      Set.range (fun t : K => gaParameterPoint y t) := by
  have hy' : (⟨gaAffineGroupTangent y, hy⟩ : W) ≠ 0 := by
    intro he
    exact hy0 (congrArg Subtype.val he)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hy').mp hW
    (⟨gaAffineGroupTangent x, hx⟩ : W)
  have hxy : gaAffineGroupTangent x = c • gaAffineGroupTangent y :=
    (congrArg Subtype.val hc).symm
  have hc0 : c ≠ 0 := by
    intro he
    exact hx0 (hxy.trans ((congrArg (fun a : K => a • gaAffineGroupTangent y) he).trans
      (zero_smul K (gaAffineGroupTangent y))))
  exact gaParameterPoint_range_of_smul x y c hc0 hxy

end
end ReductiveGroups
