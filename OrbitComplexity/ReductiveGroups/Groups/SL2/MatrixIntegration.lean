import OrbitComplexity.ReductiveGroups.Groups.SL2.BinaryBlocks
import Mathlib.Algebra.Lie.Matrix

/-! # Algebraic integration of finite matrix representations of `sl₂` -/

noncomputable section

namespace ReductiveGroups

open TauCeti LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

universe u
variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]

/-- A finite matrix representation of `sl₂` is the differential of a morphism from `SL₂`. -/
theorem exists_sl2_matrixMap {n : ℕ}
    (r : SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ Matrix (Fin n) (Fin n) K) :
    ∃ φ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K]
        TauCeti.SpecialLinear.coordinateHopfAlgebra K 2,
      ∀ x : SpecialLinear.sl (Fin 2) K,
        affineGroupMatrixDifferential n φ
          ((TauCeti.SpecialLinear.tangentLieEquivSl (R := K) (B := K) 2).symm x) = r x := by
  let ρ := (lieEquivMatrix' (R := K) (n := Fin n)).symm.toLieHom.comp r
  let := LieRingModule.compLieHom (Fin n → K) ρ
  let := LieModule.compLieHom (Fin n → K) ρ
  obtain ⟨φ, hφ⟩ := BinaryForms.exists_coordinateMap_differential K (Pi.basisFun K (Fin n))
  refine ⟨φ, fun x => ?_⟩
  rw [hφ, LinearMap.toMatrix_eq_toMatrix']
  have he : LieModule.toEnd K (SpecialLinear.sl (Fin 2) K) (Fin n → K) x = ρ x := by
    apply LinearMap.ext
    intro v
    rfl
  rw [he]
  change (lieEquivMatrix' (R := K) (n := Fin n))
    ((lieEquivMatrix' (R := K) (n := Fin n)).symm (r x)) = r x
  exact LieEquiv.apply_symm_apply _ _

end ReductiveGroups
