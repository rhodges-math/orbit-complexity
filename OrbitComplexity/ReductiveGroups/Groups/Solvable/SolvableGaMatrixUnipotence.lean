import OrbitComplexity.ReductiveGroups.Groups.Solvable.SolvableLieTriangularBasis
import OrbitComplexity.ReductiveGroups.Groups.Representations.UpperMatrixGap
import OrbitComplexity.ReductiveGroups.Lie.Exponential.NilpotentExponentialConjugation

/-!
# Solvable Ga Matrix Unipotence

Nilpotent elements of a common triangular Lie representation have
uniformly unipotent products of their exponentials. -/

noncomputable section
namespace ReductiveGroups

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

omit [CharZero K] in
private theorem upperGap_zero_one :
    matrixUpperGap 0 (1 : Matrix (Fin n) (Fin n) K) := by
  intro i j hij
  simp [Fin.ne_of_gt hij]

omit [CharZero K] in
private theorem upperGap_zero_pow {A : Matrix (Fin n) (Fin n) K}
    (hA : matrixUpperGap 0 A) (m : ℕ) : matrixUpperGap 0 (A ^ m) := by
  induction m with
  | zero => simpa using (upperGap_zero_one (K := K) (n := n))
  | succ m ih =>
      rw [pow_succ]
      simpa using matrixUpperGap_mul ih hA

omit [CharZero K] in
private theorem upper_mul_diag_pow {A : Matrix (Fin n) (Fin n) K}
    (hA : matrixUpperGap 0 A) (m : ℕ) (i : Fin n) :
    (A ^ m) i i = (A i i) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, upperMatrix_mul_diag (upperGap_zero_pow hA m) hA, ih, pow_succ]

omit [CharZero K] in
/-- A nilpotent upper-triangular matrix has zero diagonal. -/
theorem matrixUpperGap_one_of_nilpotent_upper
    {A : Matrix (Fin n) (Fin n) K}
    (hupper : matrixUpperGap 0 A) (hnil : IsNilpotent A) :
    matrixUpperGap 1 A := by
  obtain ⟨m, hm⟩ := hnil
  intro i j hij
  by_cases hji : j = i
  · subst j
    have hd : (A i i) ^ m = 0 := by
      rw [← upper_mul_diag_pow hupper m i, hm]
      simp
    exact eq_zero_of_pow_eq_zero hd
  · exact hupper i j (by
      have : j.val ≠ i.val := fun h => hji (Fin.ext h)
      omega)

private def strictUpperMatrices : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {A | matrixUpperGap 1 A}
  zero_mem' := by intro i j hij; simp
  add_mem' := by
    intro A B hA hB i j hij
    simp [hA i j hij, hB i j hij]
  smul_mem' := by
    intro c A hA i j hij
    simp [hA i j hij]

omit [CharZero K] in
private theorem strictUpperMatrices_mul
    {A B : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ strictUpperMatrices (K := K) (n := n))
    (hB : B ∈ strictUpperMatrices (K := K) (n := n)) :
    A * B ∈ strictUpperMatrices (K := K) (n := n) :=
  matrixUpperGap_mono (matrixUpperGap_mul hA hB) (by omega)

omit [CharZero K] in
private theorem strictUpperMatrices_pow
    {A : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ strictUpperMatrices (K := K) (n := n)) (m : ℕ) :
    A ^ (m + 1) ∈ strictUpperMatrices (K := K) (n := n) := by
  induction m with
  | zero => simpa using hA
  | succ m ih =>
      rw [pow_succ]
      exact strictUpperMatrices_mul ih hA

/-- Finite exponential of a strictly upper triangular matrix differs from
one by a strictly upper triangular matrix. -/
theorem matrixUpperGap_exp_sub_one
    {A : Matrix (Fin n) (Fin n) K}
    (hA : matrixUpperGap 1 A) (hnil : IsNilpotent A) :
    matrixUpperGap 1 (associativeExponential (K := K) A - 1) := by
  let : Algebra ℚ K := (Rat.castHom K).toAlgebra
  let : Module ℚ (Matrix (Fin n) (Fin n) K) :=
    Module.compHom (Matrix (Fin n) (Fin n) K) (algebraMap ℚ K)
  obtain ⟨m, hm⟩ := hnil
  have hm' : A ^ (m + 1) = 0 := pow_eq_zero_of_le (Nat.le_succ m) hm
  change IsNilpotent.exp A - 1 ∈ strictUpperMatrices (K := K) (n := n)
  rw [IsNilpotent.exp_eq_sum hm', Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    add_sub_cancel_right]
  apply Submodule.sum_mem
  intro i hi
  change (algebraMap ℚ K (((i + 1).factorial : ℚ)⁻¹) • A ^ (i + 1)) ∈
    strictUpperMatrices (K := K) (n := n)
  exact (strictUpperMatrices (K := K) (n := n)).smul_mem _
    (strictUpperMatrices_pow hA i)

private theorem strictUpperMatrices_prod_sub_one
    (xs : List (Matrix (Fin n) (Fin n) K))
    (hxs : ∀ A ∈ xs,
      associativeExponential (K := K) A - 1 ∈
        strictUpperMatrices (K := K) (n := n)) :
    (xs.map (associativeExponential (K := K))).prod - 1 ∈
      strictUpperMatrices (K := K) (n := n) := by
  induction xs with
  | nil => simp
  | cons A xs ih =>
      let E := associativeExponential (K := K) A
      let P := (xs.map (associativeExponential (K := K))).prod
      have hE : E - 1 ∈ strictUpperMatrices (K := K) (n := n) :=
        hxs A (List.mem_cons_self)
      have hP : P - 1 ∈ strictUpperMatrices (K := K) (n := n) :=
        ih (fun B hB => hxs B (List.mem_cons_of_mem _ hB))
      have hident : E * P - 1 = (E - 1) + (P - 1) + (E - 1) * (P - 1) := by
        noncomm_ring
      simpa only [List.map_cons, List.prod_cons, E, P, hident] using
        (strictUpperMatrices (K := K) (n := n)).add_mem
          ((strictUpperMatrices (K := K) (n := n)).add_mem hE hP)
          (strictUpperMatrices_mul hE hP)

omit [CharZero K] in
private theorem strictUpperMatrices_pow_eq_zero
    {A : Matrix (Fin n) (Fin n) K}
    (hA : matrixUpperGap 1 A) : A ^ n = 0 := by
  have hpow (m : ℕ) : matrixUpperGap m (A ^ m) := by
    induction m with
    | zero => simpa using (upperGap_zero_one (K := K) (n := n))
    | succ m ih =>
        rw [pow_succ]
        exact matrixUpperGap_mul ih hA
  exact matrixUpperGap_eq_zero (hpow n) le_rfl

/-- The same exponent `n` kills the deviation from identity of every
product of exponentials of nilpotent upper-triangular matrices. -/
theorem SolvableGaMatrixUnipotence.nilpotent_exponential_product_unipotent
    (xs : List (Matrix (Fin n) (Fin n) K))
    (hxs : ∀ A ∈ xs, matrixUpperGap 0 A ∧ IsNilpotent A) :
    ((xs.map (associativeExponential (K := K))).prod - 1) ^ n = 0 := by
  apply strictUpperMatrices_pow_eq_zero
  apply strictUpperMatrices_prod_sub_one xs
  intro A hA
  exact matrixUpperGap_exp_sub_one
    (matrixUpperGap_one_of_nilpotent_upper (hxs A hA).1 (hxs A hA).2)
    (hxs A hA).2

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lie's theorem supplies one basis in which every element of a solvable
Lie algebra acts upper triangularly. If selected represented elements are
nilpotent, arbitrary products of their exponentials are uniformly unipotent. -/
theorem SolvableLie.nilpotent_exponential_product_unipotent
    [IsAlgClosed K]
    {S : Type*} [LieRing S] [LieAlgebra K S] [LieAlgebra.IsSolvable S]
    (f : S →ₗ⁅K⁆ Matrix (Fin n) (Fin n) K)
    (xs : List S) (hxs : ∀ z ∈ xs, IsNilpotent (f z)) :
    ((xs.map (fun z => associativeExponential (K := K) (f z))).prod - 1) ^ n = 0 := by
  let fEnd : S →ₗ⁅K⁆ Module.End K (Fin n → K) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
      Module.End K (Fin n → K)).toAlgHom.toLieHom.comp f
  let _ : LieRingModule S (Fin n → K) := LieRingModule.compLieHom (Fin n → K) fEnd
  let _ : LieModule K S (Fin n → K) := LieModule.compLieHom (Fin n → K) fEnd
  have hact (z : S) (v : Fin n → K) :
      ⁅z, v⁆ = Matrix.toLin' (f z) v := by rfl
  obtain ⟨b, hb⟩ := SolvableLieTriangularBasis.exists_upperTriangular_matrix_basis K S n
  let e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
      Module.End K (Fin n → K)).trans (LinearMap.toMatrixAlgEquiv b)
  have he (z : S) : matrixUpperGap 0 (e (f z)) := by
    change matrixUpperGap 0 (LinearMap.toMatrix b b (Matrix.toLin' (f z)))
    intro i j hij
    rw [LinearMap.toMatrix_apply]
    change b.repr (Matrix.toLin' (f z) (b j)) i = 0
    rw [← hact z]
    exact hb z i j hij
  have hnil (z : S) (hz : z ∈ xs) : IsNilpotent (e (f z)) :=
    (hxs z hz).map e.toAlgHom
  have htrans := SolvableGaMatrixUnipotence.nilpotent_exponential_product_unipotent
    (K := K) (n := n) (xs.map (fun z => e (f z))) (by
      intro A hA
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hA
      exact ⟨he z, hnil z hz⟩)
  apply e.injective
  simp only [map_pow, map_sub, map_one, map_zero, map_list_prod, List.map_map,
    Function.comp_def] at htrans ⊢
  let : Algebra ℚ K := (Rat.castHom K).toAlgebra
  let : Module ℚ (Matrix (Fin n) (Fin n) K) :=
    Module.compHom (Matrix (Fin n) (Fin n) K) (algebraMap ℚ K)
  have hlist : (xs.map (fun z => e (associativeExponential (K := K) (f z)))) =
      xs.map (fun z => associativeExponential (K := K) (e (f z))) := by
    apply List.map_congr_left
    intro z hz
    exact IsNilpotent.map_exp (hxs z hz) e.toAlgHom
  change ((xs.map (fun z => e (associativeExponential (K := K) (f z)))).prod - 1) ^ n = 0
  rw [hlist]
  exact htrans

end ReductiveGroups
