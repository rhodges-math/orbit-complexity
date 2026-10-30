import OrbitComplexity.BruhatIntervals.Realizations.Embedding

/-!
# A Coxeter extension by two simple roots

Two additional simple roots can read two chosen coordinates of the original geometric space.
Their links have exponent zero at the selected old indices and exponent two at the other indices.
The old Coxeter system embeds as the standard parabolic subgroup on its original indices.

## Main definitions

* `pairExtensionMatrix`: the Coxeter matrix obtained by adjoining the two indices.

## Main results

* `pairExtension_form_left`: the first new root reads the negative of the first coordinate.
* `pairExtension_form_right`: the second new root reads the negative of the second coordinate.
* `pairExtension_pairing_det`: the resulting pairing determinant is the selected coordinate.
* `pairExtension_embedding`: the old group embeds as a standard parabolic subgroup, preserving
  length and intertwining the geometric actions.

## Implementation notes

The construction does not require a nondegenerate original form. A nonzero coordinate outside
one selected simple root supplies a nonzero two-by-two pairing determinant.

## References

* M. Dyer, *On the Bruhat graph of a Coxeter system*, Compositio Mathematica 78 (1991),
  Lemma 3.1.
-/

namespace BruhatIntervals

attribute [local instance] Classical.propDecidable

variable {Index : Type*} (matrix : CoxeterMatrix Index)

/-- Adjoin two simple indices, each linked by exponent zero to one chosen old index. -/
noncomputable def pairExtensionMatrix (i j : Index) : CoxeterMatrix (Index ⊕ Bool) := by
  classical
  let attach : Bool → Index := fun b => if b then j else i
  let entries : Matrix (Index ⊕ Bool) (Index ⊕ Bool) ℕ := fun row col =>
    match row, col with
    | Sum.inl a, Sum.inl b => matrix a b
    | Sum.inl a, Sum.inr b => if a = attach b then 0 else 2
    | Sum.inr a, Sum.inl b => if b = attach a then 0 else 2
    | Sum.inr a, Sum.inr b => if a = b then 1 else 2
  refine ⟨entries, ?_, ?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro row col
    cases row with
    | inl a =>
      cases col with
      | inl b => exact matrix.symmetric b a
      | inr b => rfl
    | inr a =>
      cases col with
      | inl b => rfl
      | inr b => simp only [entries, eq_comm]
  · intro row
    cases row <;> simp only [entries, matrix.diagonal, ite_true]
  · intro row col hne
    cases row with
    | inl a =>
      cases col with
      | inl b =>
        exact matrix.off_diagonal a b (fun hab => hne (congrArg Sum.inl hab))
      | inr b =>
        change (if a = attach b then 0 else 2) ≠ 1
        split_ifs <;> norm_num
    | inr a =>
      cases col with
      | inl b =>
        change (if b = attach a then 0 else 2) ≠ 1
        split_ifs <;> norm_num
      | inr b =>
        have hab : a ≠ b := fun h => hne (congrArg Sum.inr h)
        simp [entries, hab]

/-- The extension preserves every entry between original simple indices. -/
theorem pairExtensionMatrix_old (i j k l : Index) :
    pairExtensionMatrix matrix i j (Sum.inl k) (Sum.inl l) = matrix k l := rfl

/-- The first new simple index has exponent zero only at its selected index. -/
theorem pairExtensionMatrix_left (i j k : Index) :
    pairExtensionMatrix matrix i j (Sum.inr false) (Sum.inl k) =
      if k = i then 0 else 2 := rfl

/-- The second new simple index has exponent zero only at its selected index. -/
theorem pairExtensionMatrix_right (i j k : Index) :
    pairExtensionMatrix matrix i j (Sum.inr true) (Sum.inl k) =
      if k = j then 0 else 2 := rfl

/-- The first new simple root pairs with an old vector by its negative selected
coordinate. -/
theorem pairExtension_form_left (i j : Index) (x : Index →₀ ℝ) :
    geometricForm (pairExtensionMatrix matrix i j) (geometricRoot (Sum.inr false))
      (Finsupp.lmapDomain ℝ ℝ Sum.inl x) = -x i := by
  classical
  have hlinear :
      (geometricForm (pairExtensionMatrix matrix i j) (geometricRoot (Sum.inr false))).comp
        (Finsupp.lmapDomain ℝ ℝ Sum.inl) = -(Finsupp.lapply i) := by
    apply Finsupp.lhom_ext
    intro k c
    simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      geometricForm, geometricRoot, Finsupp.linearCombination_single, one_smul,
      LinearMap.neg_apply, Finsupp.lapply_apply]
    rw [pairExtensionMatrix_left]
    by_cases hki : k = i
    · subst k
      simp only [ite_true, Nat.cast_zero, div_zero, Real.cos_zero, smul_eq_mul, mul_neg,
        mul_one, Finsupp.single_eq_same]
    · simp only [hki, ite_false, Nat.cast_ofNat, Real.cos_pi_div_two, neg_zero, smul_zero,
        Finsupp.single_eq_of_ne (Ne.symm hki)]
  exact LinearMap.congr_fun hlinear x

/-- The second new simple root pairs with an old vector by its negative selected
coordinate. -/
theorem pairExtension_form_right (i j : Index) (x : Index →₀ ℝ) :
    geometricForm (pairExtensionMatrix matrix i j) (geometricRoot (Sum.inr true))
      (Finsupp.lmapDomain ℝ ℝ Sum.inl x) = -x j := by
  classical
  have hlinear :
      (geometricForm (pairExtensionMatrix matrix i j) (geometricRoot (Sum.inr true))).comp
        (Finsupp.lmapDomain ℝ ℝ Sum.inl) = -(Finsupp.lapply j) := by
    apply Finsupp.lhom_ext
    intro k c
    simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      geometricForm, geometricRoot, Finsupp.linearCombination_single, one_smul,
      LinearMap.neg_apply, Finsupp.lapply_apply]
    rw [pairExtensionMatrix_right]
    by_cases hkj : k = j
    · subst k
      simp only [ite_true, Nat.cast_zero, div_zero, Real.cos_zero, smul_eq_mul, mul_neg,
        mul_one, Finsupp.single_eq_same]
    · simp only [hkj, ite_false, Nat.cast_ofNat, Real.cos_pi_div_two, neg_zero, smul_zero,
        Finsupp.single_eq_of_ne (Ne.symm hkj)]
  exact LinearMap.congr_fun hlinear x

/-- The determinant pairing an old simple root and a vector with the two new roots
is the second selected coordinate of the vector. -/
theorem pairExtension_pairing_det (i j : Index) (x : Index →₀ ℝ) (hij : i ≠ j) :
    let form := geometricForm (pairExtensionMatrix matrix i j)
    let old := Finsupp.lmapDomain ℝ ℝ Sum.inl (geometricRoot i)
    let translated := Finsupp.lmapDomain ℝ ℝ Sum.inl x
    let first := geometricRoot (Sum.inr false)
    let second := geometricRoot (Sum.inr true)
    form old first * form translated second - form old second * form translated first = x j := by
  dsimp only
  rw [(geometricForm_isSymm (pairExtensionMatrix matrix i j)).eq
      (Finsupp.lmapDomain ℝ ℝ Sum.inl (geometricRoot i)) (geometricRoot (Sum.inr false)),
    (geometricForm_isSymm (pairExtensionMatrix matrix i j)).eq
      (Finsupp.lmapDomain ℝ ℝ Sum.inl x) (geometricRoot (Sum.inr true)),
    (geometricForm_isSymm (pairExtensionMatrix matrix i j)).eq
      (Finsupp.lmapDomain ℝ ℝ Sum.inl (geometricRoot i)) (geometricRoot (Sum.inr true)),
    (geometricForm_isSymm (pairExtensionMatrix matrix i j)).eq
      (Finsupp.lmapDomain ℝ ℝ Sum.inl x) (geometricRoot (Sum.inr false))]
  rw [pairExtension_form_left matrix i j, pairExtension_form_right matrix i j,
    pairExtension_form_right matrix i j, pairExtension_form_left matrix i j]
  simp only [geometricRoot, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (Ne.symm hij), neg_zero,
    zero_mul, sub_zero, neg_mul_neg, one_mul]

/-- The original Coxeter system embeds as a standard parabolic subgroup of the extension,
preserving length and intertwining the geometric actions. -/
theorem pairExtension_embedding {W : Type*} [Group W] (cs : CoxeterSystem matrix W)
    (i j : Index) :
    let extended := pairExtensionMatrix matrix i j
    let system := extended.toCoxeterSystem
    ∃ embedding : W →* extended.Group,
      Function.Injective embedding ∧
      (∀ k : Index, embedding (cs.simple k) = system.simple (Sum.inl k)) ∧
      embedding.range = system.parabolic (Set.range Sum.inl) ∧
      (∀ w : W, system.length (embedding w) = cs.length w) ∧
      (∀ (w : W) (x : Index →₀ ℝ),
        Finsupp.lmapDomain ℝ ℝ Sum.inl (geometricAction matrix cs w x) =
          geometricAction extended system (embedding w)
            (Finsupp.lmapDomain ℝ ℝ Sum.inl x)) := by
  dsimp only
  refine ⟨matrixHom cs (pairExtensionMatrix matrix i j).toCoxeterSystem Sum.inl
    (pairExtensionMatrix_old matrix i j), ?_, ?_, ?_, ?_, ?_⟩
  · exact matrixHom_injective _ _ _ _
  · exact matrixHom_simple _ _ _ _
  · exact matrixHom_range _ _ _ _
  · exact matrixHom_length _ _ _ _
  · exact matrixHom_geometricAction _ _ _ _

end BruhatIntervals
