import OrbitComplexity.Paper.Deodhar.GeneralParameters
import OrbitComplexity.GroupActions.Complexity.Toric

/-! # Complexity of Deodhar parameters

The full-rank general locus and the dimension of the parameter open compute the minimum
torus orbit codimension.
-/

open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety BruhatIntervals
noncomputable section
namespace SchubertOrbits
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] torusReduced

/-- The torus complexity of the parameter variety is its coordinate count minus its weight rank. -/
theorem deodharParameter_complexity :
    letI := deodharParameterAction G expression
    torusComplexity G (deodharParameters G expression) =
      Nat.card (deodharIndex G expression) -
        subwordWeightDim (weylRealization G.rootBase) expression := by
  let := deodharParameterAction G expression
  obtain ⟨x, hx⟩ := (deodharGeneral_properties G expression).2.2.2.1
  have hr := (deodharGeneral_properties G expression).2.2.2.2 x hx
  have hd : (deodharParameters G expression).natDim = Nat.card (deodharIndex G expression) :=
    ENat.natCast_inj.mp (WithBot.coe_inj.mp
      ((deodharParameters G expression).natDim_cast.trans (deodharParameters_dim G expression)))
  obtain ⟨y, hy⟩ := exists_orbitCodim_eq (torusVariety G) (deodharParameters G expression)
  have hmin := minOrbitCodim_le (torusVariety G) (deodharParameters G expression) x
  have hbound := deodharParameter_orbit_le G expression y
  have hdim := orbitNatDim_le (torusVariety G) (deodharParameters G expression) x
  change (deodharParameters G expression).natDim -
      (orbitNatDim (torusVariety G) (deodharParameters G expression) y : ℤ) =
        (minOrbitCodim (torusVariety G) (deodharParameters G expression) : ℤ) at hy
  change (minOrbitCodim (torusVariety G) (deodharParameters G expression) : ℤ) ≤
    (deodharParameters G expression).natDim -
      (orbitNatDim (torusVariety G) (deodharParameters G expression) x : ℤ) at hmin
  rw [hr, hd] at hmin hdim
  rw [hd] at hy
  change minOrbitCodim (torusVariety G) (deodharParameters G expression) = _
  omega

end SchubertOrbits
