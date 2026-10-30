import OrbitComplexity.ReductiveGroups.Lie.Cartan.CartanQuotient
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRadicalQuotient
import Mathlib.Algebra.Lie.Weights.Killing

/-!
# Central Radical Cartan Nilpotent

In a reductive Lie algebra, a Cartan vector with nilpotent adjoint
action is central. Only the center quotient is assumed Killing,
and that property is proved from the original central-radical hypothesis. -/

noncomputable section
namespace ReductiveGroups

variable {K L Q : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [LieRing Q] [LieAlgebra K Q]

/-- Nilpotence of an adjoint action descends along a surjective
Lie homomorphism. -/
theorem ad_map_isNilpotent_of_surjective
    (f : L →ₗ⁅K⁆ Q) (hf : Function.Surjective f) (x : L)
    (hx : IsNilpotent (LieAlgebra.ad K L x)) :
    IsNilpotent (LieAlgebra.ad K Q (f x)) := by
  have hpow (n : ℕ) (y : L) :
      f (((LieAlgebra.ad K L x)^n) y) =
        ((LieAlgebra.ad K Q (f x))^n) (f y) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply]
      change f ⁅x, ((LieAlgebra.ad K L x)^n) y⁆ =
        ⁅f x, ((LieAlgebra.ad K Q (f x))^n) (f y)⁆
      rw [LieHom.map_lie, ih]
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  ext z
  obtain ⟨y, rfl⟩ := hf z
  rw [← hpow, hn, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

/-- A nilpotent adjoint direction in a Cartan subalgebra of a
finite-dimensional reductive Lie algebra belongs to the center.
The possibly nonzero center is retained. -/
theorem CentralRadical.cartan_nilpotent_ad_mem_center
    [CharZero K] [Module.Finite K L] [LieAlgebra.HasCentralRadical K L]
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    (x : L) (hx : x ∈ H) (hn : IsNilpotent (LieAlgebra.ad K L x)) :
    x ∈ LieAlgebra.center K L := by
  let q := centerQuotientLieHom (K := K) (L := L)
  let := centralRadical_centerQuotient_isKilling (K := K) (L := L)
  have hker : (q.ker : LieSubalgebra K L) ≤ H := by
    dsimp only [q]
    rw [centerQuotientLieHom_ker]
    exact center_le_cartan H
  let := cartan_map_of_surjective q centerQuotientLieHom_surjective H hker
  have hxq : q x ∈ H.map q := (H.mem_map q (q x)).mpr ⟨x, hx, rfl⟩
  have hnq := ad_map_isNilpotent_of_surjective q centerQuotientLieHom_surjective x hn
  have hz := LieAlgebra.IsKilling.eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra
    K (L ⧸ LieAlgebra.center K L) (H.map q) hxq hnq
  exact (LieSubmodule.Quotient.mk_eq_zero (N := LieAlgebra.center K L) (m := x)).mp hz

end ReductiveGroups
