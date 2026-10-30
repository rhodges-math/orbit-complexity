import OrbitComplexity.ReductiveGroups.Lie.Roots.RootStringNonvanishing
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicTripleBondExpression

/-!
# Triple Bond Root Expression Nonvanishing

The Case 2 root expression yields a nonzero iterated Lie bracket
under an explicit additive realization of the abstract root pairing in
the roots of a split semisimple Lie algebra. This does not identify an
arbitrary reductive group's root datum with that Lie algebra. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [IsTriangularizable K H L]

omit [CharZero R] [IsDomain R] [Finite ι] [P.IsCrystallographic]
    [P.IsReduced] [CharZero K] [LieAlgebra.IsKilling K L]
    [FiniteDimensional K L] [IsTriangularizable K H L] in
private theorem realized_weight_of_root_vector_eq
    (Φ : M →+ (H → K)) (ρ : ι → Weight K H L)
    (hρ : ∀ ξ : ι, (ρ ξ : H → K) = Φ (P.root ξ))
    (δ τ q : ι) (j : ℕ)
    (h : P.root δ = P.root τ + (j : ℤ) • P.root q) :
    (ρ δ : H → K) = (ρ τ : H → K) + (j : ℤ) • (ρ q : H → K) := by
  rw [hρ δ, hρ τ, hρ q, h]
  simp only [map_add, map_zsmul]

omit [Finite ι] [CharZero K] [LieAlgebra.IsKilling K L]
    [FiniteDimensional K L] [IsTriangularizable K H L] in
/-- Nonzero root vectors required by the Case 2 theorem can be chosen
from the nonzero Lie weight spaces; their existence is not an
additional structural premise. -/
theorem exists_nonzero_root_vectors_for_weights
    (ρ : ι → Weight K H L) :
    ∃ e : ι → L,
      ∀ ξ : ι, e ξ ∈ rootSpace H (ρ ξ) ∧ e ξ ≠ 0 := by
  classical
  choose e he using fun ξ => (ρ ξ).exists_ne_zero
  exact ⟨e, he⟩

/-- Under a coherent additive realization `Φ` of every abstract root
vector as a nonzero Lie root weight `ρ`, and chosen nonzero
vectors in those root spaces, every parabolic G2 Case 2
expression supplies a nonzero iterated adjoint power. -/
theorem TripleBondRootExpressionNonvanishing.expression_iterated_lie_ne_zero
    (b : P.Base) (J : Set b.support) (a : P.weylGroup)
    (ha : a ∈ standardParabolicSubgroup b J)
    (word : List b.support) (hword : word.Nodup)
    (hd : IsMinimalLeftParabolic b J (simpleWeylWord b word))
    (D : Set ι)
    (hD : D ⊆ leftRootInversionIndices b (simpleWeylWord b word))
    (β : ι)
    (hβ : β ∈ leftRootInversionIndices b (simpleWeylWord b word))
    (hβD : β ∉ D)
    (p q : b.support)
    (hp : p ∈ simpleRootSupportInt b β)
    (hq : q ∈ simpleRootSupportInt b β)
    (hpq : P.pairingIn ℤ (p : ι) (q : ι) = -3)
    (hqp : P.pairingIn ℤ (q : ι) (p : ι) = -1)
    (hbad : ¬ ∀ k : b.support,
      simpleRootCoeffInt b β k = 0 ∨ simpleRootCoeffInt b β k = 1)
    (s : Multiset ι)
    (hs : RootExpression P (parabolicAuxiliaryRootIndices b J a) D β s)
    (Φ : M →+ (H → K)) (ρ : ι → Weight K H L)
    (hρ : ∀ ξ : ι, (ρ ξ : H → K) = Φ (P.root ξ))
    (hρnz : ∀ ξ : ι, (ρ ξ).IsNonZero)
    (e : ι → L)
    (he : ∀ ξ : ι, e ξ ∈ rootSpace H (ρ ξ) ∧ e ξ ≠ 0) :
    ∃ (τ : ι) (m : ℕ),
      τ ∈ parabolicAuxiliaryRootIndices b J a ∧
      (q : ι) ∈ D ∧ 1 ≤ m ∧ m ≤ 3 ∧
      s = {τ} + Multiset.replicate m (q : ι) ∧
      P.root β = P.root τ + (m : ℤ) • P.root (q : ι) ∧
      ((toEnd K L L (e (q : ι))) ^ m) (e τ) ≠ 0 := by
  obtain ⟨τ, m, hτA, hqD, hmpos, hmle, hsform, _hτp, _hτq,
    hβroot, hstring⟩ :=
    ParabolicTripleBondExpression.root_expression_shape b J a ha word hword hd D hD
      β hβ hβD p q hp hq hpq hqp hbad s hs
  let σ (j : Fin (m + 1)) : ι := Classical.choose (hstring j.val (by omega))
  have hσ (j : Fin (m + 1)) :
      P.root (σ j) = P.root τ + (j.val : ℤ) • P.root (q : ι) :=
    (Classical.choose_spec (hstring j.val (by omega))).2
  have hσ0 : σ 0 = τ := by
    apply P.root.injective
    simpa using hσ 0
  let γ (j : Fin (m + 1)) : Weight K H L := ρ (σ j)
  have hγ0 : γ 0 = ρ τ := congrArg ρ hσ0
  have hγnz : ∀ j, (γ j).IsNonZero := fun j => hρnz (σ j)
  have hγstep : ∀ (j : ℕ) (hj : j < m),
      (γ ⟨j + 1, by omega⟩ : H → K) =
        (ρ (q : ι) : H → K) + (γ ⟨j, by omega⟩ : H → K) := by
    intro j hj
    have hprev := realized_weight_of_root_vector_eq Φ ρ hρ
      (σ ⟨j, by omega⟩) τ (q : ι) j (hσ ⟨j, by omega⟩)
    have hnext := realized_weight_of_root_vector_eq Φ ρ hρ
      (σ ⟨j + 1, by omega⟩) τ (q : ι) (j + 1)
        (hσ ⟨j + 1, by omega⟩)
    change (ρ (σ ⟨j + 1, by omega⟩) : H → K) =
      (ρ (q : ι) : H → K) + (ρ (σ ⟨j, by omega⟩) : H → K)
    rw [hnext, hprev]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel
  have hiter := RootSpace.iterated_ad_ne_zero_of_root_string
    (ρ (q : ι)) (hρnz (q : ι)) m γ hγnz hγstep
    (e (q : ι)) (e τ) (he (q : ι)).1 (he (q : ι)).2
    (by simpa only [hγ0] using (he τ).1)
    (he τ).2
  exact ⟨τ, m, hτA, hqD, hmpos, hmle, hsform, hβroot, hiter⟩

end ReductiveGroups
