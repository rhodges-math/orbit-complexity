import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootClosedSubsetGroup
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootSubsetTorus
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootPairIndependence
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootProductSupport

/-!
# Borel Root Commutator

**Chevalley commutator formula** for the root
subgroups of the Borel.

For distinct positive roots `τ, β` and root Ga points `x_τ, x_β`,
`x_τ(u) x_β(t) = (∏ x_{iτ+jβ}(c_{ij} u^i t^j)) x_β(t) x_τ(u)`, the product
running over the positive roots `iτ + jβ` with `i, j > 0`, in any fixed order,
with constants depending only on that order. The proof uses the closed-set
charts of `U`, the torus covariance of root parameters, and the weight
argument on the logarithm coordinates; it does not cite the formula. -/

noncomputable section
namespace ReductiveGroups

open TauCeti MvPolynomial

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "M" => Multiplicative (ι →₀ ℤ)

private abbrev rootTangentSpace (J : HopfIdeal K B)
    (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) := (derivationCompLieHom (B := K)
  (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (borelRootUnipotentHopfIdeal J π hπ)).hom).range

/-- The Borel root characters `τ^i β^j` with `i, j > 0`: the positive roots
`iτ + jβ` of the commutator formula. -/
def commutatorRootSet {J : HopfIdeal K B} {π : B →ₐc[K] MonoidAlgebra K M}
    (τ β : borelRootCharacterIndex J π) : Set (borelRootCharacterIndex J π) :=
  {γ | ∃ i j : ℕ, 0 < i ∧ 0 < j ∧ γ.val = τ.val ^ i * β.val ^ j}

omit [IsAlgClosed K] [CharZero K] [Finite ι] in
/-- For these parameters,

```lean
IsBorelRootCharacterClosed J π (commutatorRootSet τ β)
```
-/
theorem commutatorRootSet_closed {J : HopfIdeal K B} {π : B →ₐc[K] MonoidAlgebra K M}
    (τ β : borelRootCharacterIndex J π) :
    IsBorelRootCharacterClosed J π (commutatorRootSet τ β) := by
  classical
  intro m δ hm hrel
  choose i j hi hj hγ using fun γ : m.support => hm γ.property
  have hne : m ≠ 0 := by
    rintro rfl
    exact δ.property.1 (by simpa using hrel.symm)
  obtain ⟨γ₀, hγ₀⟩ := Finsupp.support_nonempty_iff.mpr hne
  let A : ℕ := ∑ γ : m.support, m γ * i γ
  let C : ℕ := ∑ γ : m.support, m γ * j γ
  have hA : 0 < A := by
    apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
    exact ⟨⟨γ₀, hγ₀⟩, Finset.mem_univ _,
      Nat.mul_pos (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hγ₀)) (hi _)⟩
  have hC : 0 < C := by
    apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
    exact ⟨⟨γ₀, hγ₀⟩, Finset.mem_univ _,
      Nat.mul_pos (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hγ₀)) (hj _)⟩
  refine ⟨A, C, hA, hC, ?_⟩
  rw [← hrel, Finsupp.prod, ← Finset.prod_coe_sort]
  calc ∏ γ : m.support, γ.val.val ^ m γ
      = ∏ γ : m.support, (τ.val ^ (m γ * i γ) * β.val ^ (m γ * j γ)) := by
        apply Finset.prod_congr rfl
        intro γ _
        rw [hγ γ, mul_pow, ← pow_mul, ← pow_mul, mul_comm (i γ), mul_comm (j γ)]
    _ = τ.val ^ A * β.val ^ C := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

/-- Exponent uniqueness for two distinct Borel root characters. -/
theorem borelRootCharacter_pow_mul_pow_inj
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    {τ β : borelRootCharacterIndex J π} (hτβ : τ ≠ β) {a b a' b' : ℕ}
    (h : τ.val ^ a * β.val ^ b = τ.val ^ a' * β.val ^ b') : a = a' ∧ b = b' := by
  have hlin := BorelRootCharacter.pair_linearIndependent I J hJI hI hJ π hπ hker hB hτβ
  rw [LinearIndependent.pair_iff] at hlin
  have h' := congrArg Multiplicative.toAdd h
  simp only [toAdd_mul, toAdd_pow] at h'
  have hrel : ((a : ℤ) - a') • Multiplicative.toAdd τ.val +
      ((b : ℤ) - b') • Multiplicative.toAdd β.val = 0 := by
    rw [sub_smul, sub_smul, natCast_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul]
    rw [sub_add_sub_comm, h', sub_self]
  obtain ⟨h1, h2⟩ := hlin _ _ hrel
  exact ⟨by omega, by omega⟩

end ReductiveGroups
