import OrbitComplexity.GroupActions.Complexity.OrbitCodimension
import Mathlib.Tactic

/-! # Complexity from an attained maximum orbit dimension

An upper bound for all orbit dimensions, attained by a specified point, determines the
minimum orbit codimension by subtraction from the ambient dimension.
-/

open CategoryTheory AlgebraicGeometry
namespace GroupActions
noncomputable section
universe u
variable {K : Type u} [Field K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver]

/-- An attained maximum orbit dimension computes the minimum orbit codimension. -/
theorem minOrbitCodim_eq_sub_max (r : ℕ)
    (hbound : ∀ y : X.points, orbitNatDim H X y ≤ r)
    (x : X.points) (hx : orbitNatDim H X x = r) :
    minOrbitCodim H X = X.natDim - r := by
  have : Nonempty X.points := ⟨x⟩
  obtain ⟨y, hy⟩ := Nat.sInf_mem
    (Set.range_nonempty (fun y : X.points => (orbitCodim H X y).toNat))
  have hyInt : orbitCodim H X y = (minOrbitCodim H X : ℤ) := by
    calc
      _ = ((orbitCodim H X y).toNat : ℤ) :=
        (Int.toNat_of_nonneg (orbitCodim_nonneg H X y)).symm
      _ = _ := congrArg (fun n : ℕ => (n : ℤ)) hy
  have hmin := minOrbitCodim_le H X x
  have hby := hbound y
  have hdim := orbitNatDim_le H X x
  change (X.natDim : ℤ) - (orbitNatDim H X y : ℤ) =
    (minOrbitCodim H X : ℤ) at hyInt
  change (minOrbitCodim H X : ℤ) ≤
    (X.natDim : ℤ) - (orbitNatDim H X x : ℤ) at hmin
  rw [hx] at hmin hdim
  omega

end
end GroupActions
