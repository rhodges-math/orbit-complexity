import OrbitComplexity.GroupActions.Actions.LocallyClosed
import OrbitComplexity.GroupActions.Complexity.OrbitCodimension
import OrbitComplexity.GroupActions.Varieties.ClosedDimension

/-! # Dense orbits and zero codimension

On an irreducible variety an orbit has codimension zero precisely when it is dense in the
underlying scheme. Thus minimum orbit codimension vanishes precisely when a dense orbit
exists.

## Main results

* `GroupActions.orbitCodim_eq_zero_iff`: zero orbit codimension is equivalent to density.
* `GroupActions.minOrbitCodim_eq_zero_iff`: zero minimum is equivalent to a dense orbit.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] (H X : Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]

/-- An orbit has codimension zero precisely when its rational image is scheme dense. -/
theorem orbitCodim_eq_zero_iff (x : X.points) : orbitCodim H X x = 0 ↔
    Dense (X.pointMap '' MulAction.orbit H.points x) := by
  rw [dense_iff_closure_eq]
  constructor
  · intro h
    apply X.closed_eq_univ isClosed_closure
    change orbitDim H X x = X.dim
    rw [← orbitNatDim_cast H X x, ← X.natDim_cast]
    exact congrArg (fun n : ℕ ↦ (n : WithBot ℕ∞))
      (Int.ofNat_inj.mp (sub_eq_zero.mp h)).symm
  · intro h
    have hdim : orbitDim H X x = X.dim := by
      change topologicalKrullDim (closure (X.pointMap '' MulAction.orbit H.points x)) = X.dim
      rw [h]
      exact (Homeomorph.Set.univ X.scheme).isHomeomorph.topologicalKrullDim_eq
    have hnat : orbitNatDim H X x = X.natDim := by
      have hcast := (orbitNatDim_cast H X x).trans (hdim.trans X.natDim_cast.symm)
      exact ENat.natCast_inj.mp (WithBot.coe_inj.mp hcast)
    simp only [orbitCodim, hnat, sub_self]

/-- Minimum orbit codimension vanishes precisely when a scheme-dense orbit exists. -/
theorem minOrbitCodim_eq_zero_iff [IsAlgClosed K] : minOrbitCodim H X = 0 ↔
    ∃ x : X.points, Dense (X.pointMap '' MulAction.orbit H.points x) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_orbitCodim_eq H X
    refine ⟨x, (orbitCodim_eq_zero_iff H X x).mp ?_⟩
    simpa only [h, Int.natCast_zero] using hx
  · rintro ⟨x, hx⟩
    have hle := minOrbitCodim_le H X x
    rw [(orbitCodim_eq_zero_iff H X x).mpr hx] at hle
    exact Int.ofNat_inj.mp (le_antisymm hle (Int.natCast_nonneg _))

end

end GroupActions
