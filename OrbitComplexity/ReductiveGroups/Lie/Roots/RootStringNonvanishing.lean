import Mathlib.Algebra.Lie.Weights.RootSystem

/-!
# Root String Nonvanishing

Bridges from roots in a split semisimple Lie algebra to
the sl₂ root-string calculation used for bracket nonvanishing. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [IsTriangularizable K H L]

/-- If the next root of an `α`-string exists, its upper-string
coefficient is positive. -/
theorem rootString_chainTopCoeff_pos_of_sum_root
    (α β δ : Weight K H L) (hα : α.IsNonZero)
    (hδ : (δ : H → K) = α + β) :
    0 < chainTopCoeff α β := by
  have hne : rootSpace H ((1 : ℤ) • α + β) ≠ ⊥ := by
    simpa only [one_zsmul, hδ] using δ.genWeightSpace_ne_bot
  have hbound := (rootSpace_zsmul_add_ne_bot_iff α β hα 1).mp hne
  omega

/-- In a finite-dimensional splitting Lie algebra with nondegenerate
Killing form, the bracket of nonzero root vectors is nonzero whenever
their sum is itself a nonzero root. Both input weights are
nonzero roots; the zero-weight case does not satisfy this assertion. -/
theorem rootSpace_lie_ne_zero_of_sum_root
    (α β δ : Weight K H L)
    (hα : α.IsNonZero) (hβ : β.IsNonZero) (_hδnz : δ.IsNonZero)
    (hδ : (δ : H → K) = α + β)
    (x y : L) (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) : ⁅x, y⁆ ≠ 0 := by
  let t := chainTopCoeff α β
  let N := chainLength α β
  have htpos : 0 < t := rootString_chainTopCoeff_pos_of_sum_root α β δ hα hδ
  have htN : t ≤ N := chainTopCoeff_le_chainLength α β
  obtain ⟨h, e, f, hsl2, he, hf⟩ :=
    exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := hsl2.h_eq_coroot hα he hf
  obtain ⟨z, hz, hz0⟩ := (chainTop α β).exists_ne_zero
  have hprim : hsl2.HasPrimitiveVectorWith z (N : K) :=
    have hmem := lie_mem_genWeightSpace_of_mem_genWeightSpace he hz
    ⟨hz0, (chainLength_smul α β hz).symm,
      by rwa [genWeightSpace_add_chainTop α β hα] at hmem⟩
  let zβ : L := ((toEnd K L L f) ^ t) z
  have hzβ0 : zβ ≠ 0 :=
    hprim.pow_toEnd_f_ne_zero_of_eq_nat rfl htN
  have hweight : t • (-(α : H → K)) +
      (chainTop α β : H → K) = (β : H → K) := by
    dsimp [t]
    rw [coe_chainTop']
    simp only [smul_neg]
    module
  have hzβ : zβ ∈ rootSpace H β := by
    have hmem := toEnd_pow_apply_mem hf hz t
    change zβ ∈ genWeightSpace L (β : H → K)
    simpa only [zβ, hweight] using hmem
  let n := t - 1
  have hnt : n + 1 = t := by dsimp [n]; omega
  have hnN : n ≤ N := by omega
  have hprev0 : ((toEnd K L L f) ^ n) z ≠ 0 :=
    hprim.pow_toEnd_f_ne_zero_of_eq_nat rfl hnN
  have htnz : (t : K) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt htpos
  have hNn : ((N : K) - (n : K)) ≠ 0 := by
    intro heq
    have hcast : (N : K) = (n : K) := sub_eq_zero.mp heq
    have hnat : N = n := Nat.cast_injective hcast
    omega
  have hfactor : (t : K) * ((N : K) - (n : K)) ≠ 0 :=
    mul_ne_zero htnz hNn
  have hformula : ⁅e, zβ⁆ =
      ((t : K) * ((N : K) - (n : K))) • ((toEnd K L L f ^ n) z) := by
    simpa only [zβ, ← hnt, Nat.cast_add, Nat.cast_one] using
      hprim.lie_e_pow_succ_toEnd_f n
  have hez : ⁅e, zβ⁆ ≠ 0 := by
    rw [hformula]
    exact smul_ne_zero hfactor hprev0
  obtain ⟨cy, hcy⟩ :=
    (finrank_eq_one_iff_of_nonzero' (⟨zβ, hzβ⟩ : rootSpace H β)
      (by simpa using hzβ0)).mp (finrank_rootSpace_eq_one β hβ) ⟨y, hy⟩
  have hyrepr : y = cy • zβ := by simpa using hcy.symm
  have hcy0 : cy ≠ 0 := by
    intro hc
    apply hy0
    simpa [hc] using hyrepr
  obtain ⟨cx, hcx⟩ :=
    (finrank_eq_one_iff_of_nonzero' (⟨e, he⟩ : rootSpace H α)
      (by simpa using hsl2.e_ne_zero)).mp
      (finrank_rootSpace_eq_one α hα) ⟨x, hx⟩
  have hxrepr : x = cx • e := by simpa using hcx.symm
  have hcx0 : cx ≠ 0 := by
    intro hc
    apply hx0
    simpa [hc] using hxrepr
  rw [hxrepr, hyrepr, smul_lie, lie_smul, smul_smul]
  exact smul_ne_zero (mul_ne_zero hcx0 hcy0) hez

/-- Iterating a nonzero root vector along a string of nonzero
roots never kills a nonzero starting root vector. The hypotheses say
that each successive weight is an existing nonzero root. -/
theorem RootSpace.iterated_ad_ne_zero_of_root_string
    (α : Weight K H L) (hα : α.IsNonZero)
    (m : ℕ) (γ : Fin (m + 1) → Weight K H L)
    (hγ : ∀ i, (γ i).IsNonZero)
    (hstep : ∀ (j : ℕ) (hj : j < m),
      (γ ⟨j + 1, by omega⟩ : H → K) =
        α + (γ ⟨j, by omega⟩ : H → K))
    (x y : L) (hx : x ∈ rootSpace H α) (hx0 : x ≠ 0)
    (hy : y ∈ rootSpace H (γ 0)) (hy0 : y ≠ 0) :
    ((toEnd K L L x) ^ m) y ≠ 0 := by
  have hall (j : ℕ) (hj : j ≤ m) :
      ((toEnd K L L x) ^ j) y ∈ rootSpace H (γ ⟨j, by omega⟩) ∧
      ((toEnd K L L x) ^ j) y ≠ 0 := by
    induction j with
    | zero =>
      simpa using (show y ∈ rootSpace H (γ 0) ∧ y ≠ 0 from ⟨hy, hy0⟩)
    | succ j ih =>
      have hjm : j ≤ m := by omega
      have hjlt : j < m := by omega
      obtain ⟨hmem, hne⟩ := ih hjm
      have hsum := hstep j hjlt
      have hnewmem : ⁅x, ((toEnd K L L x) ^ j) y⁆ ∈
          rootSpace H (γ ⟨j + 1, by omega⟩) := by
        change ⁅x, ((toEnd K L L x) ^ j) y⁆ ∈
          genWeightSpace L (γ ⟨j + 1, by omega⟩ : H → K)
        have h := lie_mem_genWeightSpace_of_mem_genWeightSpace hx hmem
        simpa only [hsum] using h
      have hnewne : ⁅x, ((toEnd K L L x) ^ j) y⁆ ≠ 0 :=
        rootSpace_lie_ne_zero_of_sum_root α
          (γ ⟨j, by omega⟩) (γ ⟨j + 1, by omega⟩)
          hα (hγ ⟨j, by omega⟩) (hγ ⟨j + 1, by omega⟩)
          hsum x _ hx hmem hx0 hne
      simpa only [pow_succ', Module.End.mul_apply, toEnd_apply_apply] using
        (show ⁅x, ((toEnd K L L x) ^ j) y⁆ ∈
            rootSpace H (γ ⟨j + 1, by omega⟩) ∧
            ⁅x, ((toEnd K L L x) ^ j) y⁆ ≠ 0 from ⟨hnewmem, hnewne⟩)
  exact (hall m (le_refl m)).2

end ReductiveGroups
