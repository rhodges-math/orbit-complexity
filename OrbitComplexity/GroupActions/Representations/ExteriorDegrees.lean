import OrbitComplexity.GroupActions.Representations.ExteriorCoaction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-! # Coactions on homogeneous exterior powers

The multiplicative exterior-algebra coaction preserves each homogeneous degree. Restricting
that coaction equips every exterior power with its induced comodule structure.
-/

noncomputable section
namespace GroupActions
open TauCeti
open scoped TensorProduct
universe u v w
variable {K : Type u} {H : Type v} {V : Type w}

section TensorImages
variable [CommRing K] [CommRing H] [Algebra K H] [AddCommGroup V] [Module K V]

private def degreeRange (d : ℕ) : Submodule K ((ExteriorAlgebra K V) ⊗[K] H) :=
  (TensorProduct.map (⋀[K]^d V).subtype (LinearMap.id : H →ₗ[K] H)).range

private theorem degreeRange_one :
    (1 : (ExteriorAlgebra K V) ⊗[K] H) ∈ degreeRange (K := K) (H := H) (V := V) 0 := by
  refine ⟨(⟨1, SetLike.one_mem_graded (fun d : ℕ => ⋀[K]^d V)⟩ : ⋀[K]^0 V) ⊗ₜ[K]
    (1 : H), ?_⟩
  simp only [TensorProduct.map_tmul, Submodule.coe_subtype, LinearMap.id_apply,
    Algebra.TensorProduct.one_def]

private theorem degreeRange_mul {i j : ℕ}
    {x y : (ExteriorAlgebra K V) ⊗[K] H} (hx : x ∈ degreeRange i) (hy : y ∈ degreeRange j) :
    x * y ∈ degreeRange (i + j) := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  induction x using TensorProduct.inductionOn with
  | tmul a h =>
      induction y using TensorProduct.inductionOn with
      | tmul b k =>
          refine ⟨(⟨a.val * b.val, SetLike.mul_mem_graded a.property b.property⟩ :
            ⋀[K]^(i + j) V) ⊗ₜ[K] (h * k), ?_⟩
          simp only [TensorProduct.map_tmul, Submodule.coe_subtype, LinearMap.id_apply,
            Algebra.TensorProduct.tmul_mul_tmul]
      | add z w hz hw =>
          rw [map_add, mul_add]
          exact (degreeRange (i + j)).add_mem hz hw
  | add z w hz hw =>
      rw [map_add, add_mul]
      exact (degreeRange (i + j)).add_mem hz hw

end TensorImages

section Coaction
variable [Field K] [CharZero K] [CommRing H] [Bialgebra K H]
  [AddCommGroup V] [Module K V] [Comodule K H V]

private theorem coact_generator_mem (v : V) :
    GroupActions.exteriorCoact (H := H) (ExteriorAlgebra.ι K v) ∈
      degreeRange (K := K) (H := H) (V := V) 1 := by
  let l : V →ₗ[K] ⋀[K]^1 V := (ExteriorAlgebra.ι K).codRestrict _ fun v => by
    simpa only [pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι K) v
  refine ⟨TensorProduct.map l LinearMap.id (Comodule.coact (R := K) (C := H) v), ?_⟩
  rw [TensorProduct.map_map]
  have hl : (⋀[K]^1 V).subtype.comp l = ExteriorAlgebra.ι K := rfl
  rw [hl, LinearMap.id_comp]
  exact (GroupActions.exteriorCoact_ι v).symm

private theorem coact_multi_mem (d : ℕ) (a : Fin d → V) :
    GroupActions.exteriorCoact (H := H) (ExteriorAlgebra.ιMulti K d a) ∈
      degreeRange (K := K) (H := H) (V := V) d := by
  induction d with
  | zero =>
      rw [ExteriorAlgebra.ιMulti_zero_apply, map_one]
      exact degreeRange_one
  | succ d ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul]
      simpa only [Nat.add_comm] using
        degreeRange_mul (coact_generator_mem (a 0)) (ih (Matrix.vecTail a))

private theorem coact_homogeneous_mem (d : ℕ) {x : ExteriorAlgebra K V}
    (hx : x ∈ ⋀[K]^d V) :
    GroupActions.exteriorCoact (H := H) x ∈
      degreeRange (K := K) (H := H) (V := V) d := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨a, rfl⟩ := ha
      exact coact_multi_mem d a
  | zero =>
      rw [map_zero]
      exact (degreeRange d).zero_mem
  | add x y _ _ hx hy =>
      rw [map_add]
      exact (degreeRange d).add_mem hx hy
  | smul r x _ hx =>
      rw [map_smul]
      exact (degreeRange d).smul_mem r hx


private def degreeSubcomodule (d : ℕ) :
    letI := GroupActions.exteriorAlgebraComodule (K := K) (H := H) (V := V)
    Subcomodule K H (ExteriorAlgebra K V) := by
  letI := GroupActions.exteriorAlgebraComodule (K := K) (H := H) (V := V)
  exact Subcomodule.ofSubmodule (⋀[K]^d V) fun _ hx => coact_homogeneous_mem d hx

/-- Each homogeneous exterior power inherits the exterior-algebra coaction. -/
@[instance_reducible]
def exteriorPowerComodule (d : ℕ) : Comodule K H (⋀[K]^d V) :=
  letI := GroupActions.exteriorAlgebraComodule (K := K) (H := H) (V := V)
  Subcomodule.instComodule (degreeSubcomodule d)

/-- Including an exterior power intertwines its coaction with the exterior-algebra coaction. -/
theorem exteriorPower_coact (d : ℕ) (x : ⋀[K]^d V) :
    TensorProduct.map (⋀[K]^d V).subtype LinearMap.id ((exteriorPowerComodule d).coact x) =
      GroupActions.exteriorCoact (H := H) x.val := by
  let := GroupActions.exteriorAlgebraComodule (K := K) (H := H) (V := V)
  exact (degreeSubcomodule d).subtype_rTensor_inducedCoact x

end Coaction
end GroupActions
