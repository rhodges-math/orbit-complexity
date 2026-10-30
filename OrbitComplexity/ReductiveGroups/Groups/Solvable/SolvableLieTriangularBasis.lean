import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Solvable Lie Triangular Basis

A common triangular basis for a finite-dimensional representation of an
arbitrary solvable Lie algebra over an algebraically closed characteristic-zero field. -/

noncomputable section
namespace ReductiveGroups
open Module

variable {K L V : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [LieAlgebra.IsSolvable L]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [LieRingModule L V] [LieModule K L V]

/-- A nonzero representation has a codimension-one invariant submodule,
obtained from a common eigenfunctional in its dual Lie module. -/
private theorem exists_invariant_eigenfunctional
    [Nontrivial V] :
    ∃ f : Module.Dual K V, f ≠ 0 ∧
      ∀ (x : L) (v : V), f v = 0 → f ⁅x, v⁆ = 0 := by
  obtain ⟨χ, hnon⟩ :=
    LieModule.exists_nontrivial_weightSpace_of_isSolvable (k := K) (L := L)
      (V := Module.Dual K V)
  obtain ⟨⟨f, hf⟩, hf0⟩ := exists_ne
    (0 : LieModule.weightSpace (Module.Dual K V) χ)
  have hfne : f ≠ 0 := by
    intro heq
    apply hf0
    exact Subtype.ext heq
  refine ⟨f, hfne, ?_⟩
  intro x v hv
  have heig := (LieModule.mem_weightSpace χ f).mp hf x
  have heval := congrArg (fun g : Module.Dual K V => g v) heig
  simpa only [Module.Dual.lie_apply, LinearMap.smul_apply, hv,
    smul_zero, neg_eq_zero] using heval

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
/-- Coordinates of a vector in the invariant hyperplane do not change when
its basis is extended by one final vector. -/
private theorem mkFinSnoc_repr_castSucc
    {n : ℕ} (N : Submodule K V) (b : Basis (Fin n) K N)
    (y : V)
    (hli : ∀ (c : K), ∀ z ∈ N, c • y + z = 0 → c = 0)
    (hsp : ∀ z : V, ∃ c : K, z + c • y ∈ N)
    (w : N) (i : Fin n) :
    (Basis.mkFinSnoc b y hli hsp).repr (w : V) (Fin.castSucc i) =
      b.repr w i := by
  let B : Basis (Fin (n + 1)) K V := Basis.mkFinSnoc b y hli hsp
  have hbasis (j : Fin n) : B (Fin.castSucc j) = (b j : V) := by
    simp [B, Basis.coe_mkFinSnoc]
  have hsum : (w : V) =
      ∑ j : Fin n, (b.repr w j) • B (Fin.castSucc j) := by
    have hw := congrArg (fun z : N => (z : V)) (b.sum_repr w).symm
    simpa only [Submodule.coe_sum, Submodule.coe_smul, hbasis] using hw
  change B.repr (w : V) (Fin.castSucc i) = _
  rw [hsum, map_sum]
  simp only [map_smul, Basis.repr_self]
  simp [Finsupp.single_apply, Fin.castSucc_inj]

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
/-- An invariant-hyperplane vector has no last coordinate in its snoc basis. -/
private theorem mkFinSnoc_repr_last
    {n : ℕ} (N : Submodule K V) (b : Basis (Fin n) K N)
    (y : V)
    (hli : ∀ (c : K), ∀ z ∈ N, c • y + z = 0 → c = 0)
    (hsp : ∀ z : V, ∃ c : K, z + c • y ∈ N)
    (w : N) :
    (Basis.mkFinSnoc b y hli hsp).repr (w : V) (Fin.last n) = 0 := by
  let B : Basis (Fin (n + 1)) K V := Basis.mkFinSnoc b y hli hsp
  have hbasis (j : Fin n) : B (Fin.castSucc j) = (b j : V) := by
    simp [B, Basis.coe_mkFinSnoc]
  have hsum : (w : V) =
      ∑ j : Fin n, (b.repr w j) • B (Fin.castSucc j) := by
    have hw := congrArg (fun z : N => (z : V)) (b.sum_repr w).symm
    simpa only [Submodule.coe_sum, Submodule.coe_smul, hbasis] using hw
  change B.repr (w : V) (Fin.last n) = 0
  rw [hsum, map_sum]
  simp

/-- Lie's theorem iterated along invariant hyperplanes.  -/
theorem exists_solvableLie_upperTriangular_basis
    (K L V : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [LieAlgebra.IsSolvable L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [LieRingModule L V] [LieModule K L V] :
    ∃ n : ℕ, ∃ b : Basis (Fin n) K V,
      ∀ (x : L) (i j : Fin n), j.val < i.val →
        b.repr ⁅x, b j⁆ i = 0 := by
  by_cases hzero : Module.finrank K V = 0
  · refine ⟨0, basisOfFinrankZero hzero, ?_⟩
    intro x i
    exact i.elim0
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero hzero)
  obtain ⟨f, hfne, hstable⟩ :=
    exists_invariant_eigenfunctional (K := K) (L := L) (V := V)
  let H : LieSubmodule K L V := {
    toSubmodule := LinearMap.ker f
    lie_mem := by
      intro x v hv
      exact hstable x v hv
  }
  have hproper : H.toSubmodule < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro heq
    exact hfne (LinearMap.ker_eq_top.mp heq)
  have hdim : Module.finrank K H < Module.finrank K V := by
    change Module.finrank K (LinearMap.ker f) < Module.finrank K V
    simpa using Submodule.finrank_lt_finrank_of_lt hproper
  obtain ⟨n, b, hb⟩ := exists_solvableLie_upperTriangular_basis K L H
  obtain ⟨y₀, hy₀⟩ : ∃ y : V, f y ≠ 0 := by
    by_contra! hh
    apply hfne
    ext v
    exact hh v
  let y : V := (f y₀)⁻¹ • y₀
  have hy : f y = 1 := by simp [y, hy₀]
  have hli : ∀ (c : K), ∀ z ∈ H.toSubmodule,
      c • y + z = 0 → c = 0 := by
    intro c z hz heq
    have hz0 : f (z : V) = 0 := hz
    have := congrArg f heq
    simpa [hy, hz0] using this
  have hsp : ∀ z : V, ∃ c : K, z + c • y ∈ H.toSubmodule := by
    intro z
    refine ⟨-f z, ?_⟩
    change f (z + (-f z) • y) = 0
    simp [hy]
  let B : Basis (Fin (n + 1)) K V :=
    Basis.mkFinSnoc (N := H.toSubmodule) b y hli hsp
  refine ⟨n + 1, B, ?_⟩
  intro x i j hji
  induction j using Fin.lastCases with
  | last =>
    simp only [Fin.val_last] at hji
    exact (Nat.not_lt.mpr (Nat.le_of_lt_succ i.isLt)) hji |>.elim
  | cast j =>
    have hbasis : B (Fin.castSucc j) = (b j : V) := by
      simp [B, Basis.coe_mkFinSnoc]
    have hw : ⁅x, B (Fin.castSucc j)⁆ ∈ H := by
      rw [hbasis]
      exact H.lie_mem (b j).property
    induction i using Fin.lastCases with
    | last =>
      exact mkFinSnoc_repr_last H.toSubmodule b y hli hsp
        ⟨⁅x, B (Fin.castSucc j)⁆, hw⟩
    | cast i =>
      have hij : j.val < i.val := by simpa using hji
      have hOld := hb x i j hij
      convert mkFinSnoc_repr_castSucc H.toSubmodule b y hli hsp
        (⁅x, b j⁆ : H) i using 1 <;> try simp [B, hbasis]
      exact hOld.symm
termination_by Module.finrank K V
decreasing_by exact hdim

/-- The same triangular basis with the canonical dimension as its index. -/
theorem SolvableLieTriangularBasis.exists_upperTriangular_finrank_basis
    (K L V : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [LieAlgebra.IsSolvable L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [LieRingModule L V] [LieModule K L V] :
    ∃ b : Basis (Fin (Module.finrank K V)) K V,
      ∀ (x : L) (i j : Fin (Module.finrank K V)), j.val < i.val →
        b.repr ⁅x, b j⁆ i = 0 := by
  obtain ⟨n, b, hb⟩ := exists_solvableLie_upperTriangular_basis K L V
  have hn : n = Module.finrank K V := by
    simpa using (Module.finrank_eq_card_basis b).symm
  subst n
  exact ⟨b, hb⟩

/-- In the standard matrix carrier the triangular basis is indexed by the
original matrix rank, including rank zero. -/
theorem SolvableLieTriangularBasis.exists_upperTriangular_matrix_basis
    (K L : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [LieAlgebra.IsSolvable L]
    (n : ℕ) [LieRingModule L (Fin n → K)]
    [LieModule K L (Fin n → K)] :
    ∃ b : Basis (Fin n) K (Fin n → K),
      ∀ (x : L) (i j : Fin n), j.val < i.val →
        b.repr ⁅x, b j⁆ i = 0 := by
  have hrank : Module.finrank K (Fin n → K) = n := by
    simp
  have h := SolvableLieTriangularBasis.exists_upperTriangular_finrank_basis K L (Fin n → K)
  rw [hrank] at h
  exact h

end ReductiveGroups
