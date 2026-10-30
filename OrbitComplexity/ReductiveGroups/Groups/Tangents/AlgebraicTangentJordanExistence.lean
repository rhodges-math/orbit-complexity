import OrbitComplexity.ReductiveGroups.Groups.Tangents.AlgebraicTangentJordan
import Mathlib.LinearAlgebra.JordanChevalley

/-!
# Algebraic Tangent Jordan Existence

The Jordan–Chevalley parts of a matrix tangent descend to the
original affine group. -/

noncomputable section
namespace ReductiveGroups
open Algebra

variable {K B : Type*} [Field K] [PerfectField K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B]

omit [IsAlgClosed K] in
/-- Matrix Jordan parts exist in the polynomial algebra of the original
matrix, so the entire matrix centralizer preserves both parts. -/
theorem matrixJordanParts (n : ℕ) (A : Matrix (Fin n) (Fin n) K) :
    ∃ N S : Matrix (Fin n) (Fin n) K,
      N + S = A ∧ Commute N S ∧ IsNilpotent N ∧
      Module.End.IsSemisimple (Matrix.toLin' S) ∧
      ∀ Y : Matrix (Fin n) (Fin n) K,
        Commute Y A → Commute Y N ∧ Commute Y S := by
  let e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) :=
    Matrix.toLinAlgEquiv'
  obtain ⟨N', hN', S', hS', hnil, hsemi, hsum⟩ :=
    (e A).exists_isNilpotent_isSemisimple
  let N := e.symm N'
  let S := e.symm S'
  have heN : e N = N' := e.apply_symm_apply N'
  have heS : e S = S' := e.apply_symm_apply S'
  have hadd : N + S = A := by
    apply e.injective
    simpa only [map_add, heN, heS] using hsum.symm
  have hcomm' : Commute N' S' :=
    commute_of_mem_adjoin_singleton_of_commute hS'
      (commute_of_mem_adjoin_self hN').symm
  have hcomm : Commute N S := by
    apply e.injective
    simpa only [map_mul, heN, heS] using hcomm'.eq
  have hn : IsNilpotent N := by
    apply (IsNilpotent.map_iff e.injective).mp
    simpa only [heN] using hnil
  refine ⟨N, S, hadd, hcomm, hn, ?_, ?_⟩
  · change Module.End.IsSemisimple (e S)
    rw [heS]
    exact hsemi
  · intro Y hYA
    have hY' : Commute (e Y) (e A) := hYA.map e.toRingHom
    constructor
    · have hYN' : Commute (e Y) N' :=
        commute_of_mem_adjoin_singleton_of_commute hN' hY'
      apply e.injective
      simpa only [map_mul, heN] using hYN'.eq
    · have hYS' : Commute (e Y) S' :=
        commute_of_mem_adjoin_singleton_of_commute hS' hY'
      apply e.injective
      simpa only [map_mul, heS] using hYS'.eq

/-- Every tangent of a closed affine subgroup of GL has original-group
nilpotent and semisimple Jordan tangents. Their matrix parts inherit its
matrix centralizer. -/
theorem algebraicTangentJordan_exists
    (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    ∃ dn ds : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K),
      dn + ds = d ∧
      IsNilpotent (TauCeti.GeneralLinear.tangentMatrix n
        (TauCeti.derivationComp (B := K) ρ dn)) ∧
      Module.End.IsSemisimple (Matrix.toLin'
        (TauCeti.GeneralLinear.tangentMatrix n
          (TauCeti.derivationComp (B := K) ρ ds))) ∧
      ∀ Y : Matrix (Fin n) (Fin n) K,
        Commute Y (TauCeti.GeneralLinear.tangentMatrix n
          (TauCeti.derivationComp (B := K) ρ d)) →
        Commute Y (TauCeti.GeneralLinear.tangentMatrix n
          (TauCeti.derivationComp (B := K) ρ dn)) ∧
        Commute Y (TauCeti.GeneralLinear.tangentMatrix n
          (TauCeti.derivationComp (B := K) ρ ds)) := by
  let A := TauCeti.GeneralLinear.tangentMatrix n
    (TauCeti.derivationComp (B := K) ρ d)
  obtain ⟨N, S, hadd, hcomm, hnil, hsemi, hcentral⟩ := matrixJordanParts n A
  obtain ⟨dn, ds, hdn, hds, hsum⟩ :=
    algebraicTangentJordan n ρ hρ d N S hadd hcomm hnil hsemi
  refine ⟨dn, ds, hsum, ?_, ?_, ?_⟩
  · rw [hdn]
    simpa only [← TauCeti.GeneralLinear.tangentLinearEquivMatrix_apply,
      LinearEquiv.apply_symm_apply] using hnil
  · rw [hds]
    simpa only [← TauCeti.GeneralLinear.tangentLinearEquivMatrix_apply,
      LinearEquiv.apply_symm_apply] using hsemi
  · intro Y hYA
    have h := hcentral Y hYA
    rw [hdn, hds]
    simpa only [← TauCeti.GeneralLinear.tangentLinearEquivMatrix_apply,
      LinearEquiv.apply_symm_apply] using h

end ReductiveGroups
