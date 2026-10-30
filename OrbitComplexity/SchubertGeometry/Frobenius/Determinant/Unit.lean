import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Function
import Mathlib.RingTheory.Flat.Basic

/-! # The original determinant section at the group unit

The Hopf counit is the pullback along the identity section. The
arithmetic coefficient is detected in the SAME flat chosen model, before
integer powers or residue primes. No empty-line frame is reconstructed here.
-/

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Restricting the SAME determinant-power global function to the
identity section of the reductive group gives the unit global function. -/
theorem positiveDetPower_unit (N : ℕ) :
    (η[(reductiveVariety G).toOver].left).appTop
      (positiveDetPowerFunction G N) = 1 := by
  have hu : η[(reductiveVariety G).toOver].left =
      Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom K G.coordinateAlgebra)) := by
    exact one_spec_asOver_spec_left
      (R := CommRingCat.of K) (A := CommRingCat.of G.coordinateAlgebra)
  rw [hu, positiveDetPowerFunction]
  let f : CommRingCat.of G.coordinateAlgebra ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (Bialgebra.counitAlgHom K G.coordinateAlgebra)
  change ((Scheme.ΓSpecIso (.of G.coordinateAlgebra)).inv ≫ (Spec.map f).appTop)
    (positiveDetPower G N) = 1
  rw [← Scheme.ΓSpecIso_inv_naturality]
  change (Scheme.ΓSpecIso (.of K)).inv
    ((Bialgebra.counitAlgHom K G.coordinateAlgebra) (positiveDetPower G N)) = 1
  rw [show (Bialgebra.counitAlgHom K G.coordinateAlgebra) (positiveDetPower G N) = 1 from
    positiveDetPower_counit G N, map_one]

/-- The unpowered coefficient retained on a flat prescribed empty-word
chart is already one over its arithmetic ring. Its comparison is the
counit evaluation of F, not a normalization on a special fibre. -/
theorem retainedDetCoefficient_unit (S : Subalgebra ℤ K)
    (B : Type u) [CommRing B] [Algebra S B] [Module.Flat S B]
    (e : K ⊗[S] B ≃ₐ[K] K) (q : B)
    (hq : e ((1 : K) ⊗ₜ[S] q) =
      Coalgebra.counit (R := K) (A := G.coordinateAlgebra) (positiveDetCoefficient G)) :
    q = 1 := by
  have hi : Function.Injective (fun b : B ↦ e ((1 : K) ⊗ₜ[S] b)) :=
    e.injective.comp
      (Algebra.TensorProduct.includeRight_injective (R := S) (A := K) (B := B)
        (show Function.Injective (algebraMap S K) from Subtype.val_injective))
  apply hi
  change e ((1 : K) ⊗ₜ[S] q) = e ((1 : K) ⊗ₜ[S] (1 : B))
  rw [hq, positiveDet_counit]
  change (1 : K) = e (1 : K ⊗[S] B)
  exact (map_one e).symm

end SchubertGeometry.DeterminantSection
