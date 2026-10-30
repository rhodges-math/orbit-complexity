import TauCeti.Algebra.Lie.Sl2.Decomposition
import TauCeti.Algebra.Lie.Sl2.Weyl.Standard
import Mathlib.Algebra.DirectSum.Module

/-! # The square of the sl₂ Weyl operator on integral weight vectors -/

noncomputable section

namespace ReductiveGroups.Sl2Square

open LieAlgebra LieModule

variable {K M : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M]

omit [CharZero K] in
private theorem diagonal_eigenvector {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K M) (H W : Module.End K M) (a c : ι → K) (q s : K)
    (hH : ∀ i, H (b i) = a i • b i) (hW : ∀ i, W (b i) = c i • b i)
    (hc : ∀ i, a i = q → c i = s) (v : M) (hv : H v = q • v) :
    W v = s • v := by
  classical
  have hs : H v = ∑ j, b.repr v j • (a j • b j) := by
    calc
      H v = H (∑ j, b.repr v j • b j) := congrArg H (b.sum_repr v).symm
      _ = _ := by simp only [map_sum, map_smul, hH]
  have hcoef (i : ι) : a i * b.repr v i = q * b.repr v i := by
    have he := congrArg (fun x => b.repr x i) hv
    rw [hs] at he
    simpa [map_sum, hH, map_smul, Finsupp.single_apply, mul_comm] using he
  conv_lhs => rw [← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr v]
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hW, smul_smul, smul_smul]
  by_cases hi : b.repr v i = 0
  · simp [hi]
  · rw [hc i (mul_right_cancel₀ hi (hcoef i)), mul_comm]

private theorem sign_of_weight (n j : ℕ) (q : ℤ)
    (hq : (n : K) - 2 * (j : K) = (q : K)) :
    (-1 : K) ^ n = (-1 : K) ^ q := by
  have hq' : (n : ℤ) - 2 * (j : ℤ) = q := by exact_mod_cast hq
  rw [← hq', zpow_sub₀ (by norm_num : (-1 : K) ≠ 0),
    zpow_mul, zpow_ofNat, neg_one_sq, one_zpow, div_one]
  exact (zpow_natCast (-1 : K) n).symm

variable [Module ℚ M]

private theorem standard_square_map (n : ℕ)
    (E F : Module.End K M) (hE : IsNilpotent E) (hF : IsNilpotent F)
    (g : TauCeti.Sl2Std K n →ₗ[K] M)
    (he : E ∘ₗ g = g ∘ₗ TauCeti.Sl2Std.raise K n)
    (hf : F ∘ₗ g = g ∘ₗ TauCeti.Sl2Std.lower K n)
    (v : TauCeti.Sl2Std K n) :
    let W := IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E
    W (W (g v)) = (-1 : K) ^ n • g v := by
  let W := IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E
  have he' := Module.End.commute_exp_left_of_commute
    (TauCeti.Sl2Std.isNilpotent_raise (K := K) (n := n)) hE he
  have hf' := Module.End.commute_exp_left_of_commute
    (TauCeti.Sl2Std.isNilpotent_lower (K := K) (n := n)).neg hF.neg
    (show (-F) ∘ₗ g = g ∘ₗ (-TauCeti.Sl2Std.lower K n) by
      ext x
      simpa using congrArg Neg.neg (LinearMap.congr_fun hf x))
  have he_apply (x) : IsNilpotent.exp E (g x) =
      g (IsNilpotent.exp (TauCeti.Sl2Std.raise K n) x) :=
    by simpa only [LinearMap.comp_apply] using LinearMap.congr_fun he' x
  have hf_apply (x) : IsNilpotent.exp (-F) (g x) =
      g (IsNilpotent.exp (-TauCeti.Sl2Std.lower K n) x) :=
    by simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hf' x
  have hw (x : TauCeti.Sl2Std K n) :
      W (g x) = g ((TauCeti.Sl2Std.weylUnit K n : Module.End K _) x) := by
    rw [TauCeti.Sl2Std.coe_weylUnit]
    change IsNilpotent.exp E (IsNilpotent.exp (-F) (IsNilpotent.exp E (g x))) = _
    rw [he_apply, hf_apply, he_apply]
    simp only [Module.End.mul_apply]
  change W (W (g v)) = _
  rw [hw, hw, TauCeti.Sl2Std.weylUnit_weylUnit_apply, map_smul]

variable [IsAlgClosed K]
  [LieRingModule (SpecialLinear.sl (Fin 2) K) M]
  [LieModule K (SpecialLinear.sl (Fin 2) K) M] [FiniteDimensional K M]

/-- The finite exponential Weyl operator squares to the parity of an integral weight. -/
theorem square_on_weight (hE : IsNilpotent
    (toEnd K (SpecialLinear.sl (Fin 2) K) M (TauCeti.slFinTwoBasis K 0)))
    (hF : IsNilpotent
    (toEnd K (SpecialLinear.sl (Fin 2) K) M (TauCeti.slFinTwoBasis K 1)))
    (q : ℤ) (v : M) (hv : ⁅TauCeti.slFinTwoBasis K 2, v⁆ = (q : K) • v) :
    let E := toEnd K (SpecialLinear.sl (Fin 2) K) M (TauCeti.slFinTwoBasis K 0)
    let F := toEnd K (SpecialLinear.sl (Fin 2) K) M (TauCeti.slFinTwoBasis K 1)
    let W := IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E
    W (W v) = (-1 : K) ^ q • v := by
  classical
  let E := toEnd K (SpecialLinear.sl (Fin 2) K) M (TauCeti.slFinTwoBasis K 0)
  let F := toEnd K (SpecialLinear.sl (Fin 2) K) M (TauCeti.slFinTwoBasis K 1)
  let H := toEnd K (SpecialLinear.sl (Fin 2) K) M (TauCeti.slFinTwoBasis K 2)
  let W := IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E
  obtain ⟨k, N, n, hint, hn⟩ := TauCeti.Sl2Std.exists_isInternal_lieModuleEquiv K M
  let phi (i : Fin k) := (hn i).some
  let g (i : Fin k) := (N i).incl.comp (phi i).symm.toLieModuleHom
  let b (i : Fin k) := (TauCeti.Sl2Std.basis K (n i)).map (phi i).symm.toLinearEquiv
  let B := hint.collectedBasis b
  have hB (i : Σ j : Fin k, Fin (n j + 1)) :
      B i = g i.1 (TauCeti.Sl2Std.basis K (n i.1) i.2) := by
    simp [B, b, g, DirectSum.IsInternal.collectedBasis_coe]
  have hH (i : Σ j : Fin k, Fin (n j + 1)) :
      H (B i) = ((n i.1 : K) - 2 * (i.2 : ℕ)) • B i := by
    rw [hB]
    change ⁅TauCeti.slFinTwoBasis K 2, g i.1 _⁆ = _
    rw [← LieModuleHom.map_lie, TauCeti.Sl2Std.lie_slFinTwoBasis_two,
      TauCeti.Sl2Std.diag_basis, map_smul]
  have hW (i : Σ j : Fin k, Fin (n j + 1)) :
      (W * W) (B i) = (-1 : K) ^ n i.1 • B i := by
    rw [hB]
    apply standard_square_map (n i.1) E F hE hF (g i.1).toLinearMap
    · ext x
      change ⁅TauCeti.slFinTwoBasis K 0, g i.1 x⁆ = _
      rw [← LieModuleHom.map_lie, TauCeti.Sl2Std.lie_slFinTwoBasis_zero]
      rfl
    · ext x
      change ⁅TauCeti.slFinTwoBasis K 1, g i.1 x⁆ = _
      rw [← LieModuleHom.map_lie, TauCeti.Sl2Std.lie_slFinTwoBasis_one]
      rfl
  exact diagonal_eigenvector B H (W * W)
    (fun i => (n i.1 : K) - 2 * (i.2 : ℕ)) (fun i => (-1 : K) ^ n i.1)
    (q : K) ((-1 : K) ^ q) hH hW
    (fun i hi => sign_of_weight (n i.1) (i.2 : ℕ) q hi) v hv

end ReductiveGroups.Sl2Square
