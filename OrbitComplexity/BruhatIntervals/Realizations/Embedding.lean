import OrbitComplexity.BruhatIntervals.Realizations.Comparison

/-!
# Embeddings of Coxeter systems

A map of simple indices preserving every Coxeter-matrix entry induces an injective group
homomorphism. Its image is the corresponding standard parabolic subgroup, it preserves Coxeter
length, and the geometric actions commute with inclusion of root coordinates.

## Main definitions

* `matrixHom`: the homomorphism induced by a map preserving the Coxeter matrix.

## Main results

* `matrixHom_injective`: the induced group map is injective.
* `matrixHom_range`: its image is the standard parabolic subgroup on the image indices.
* `matrixHom_length`: the induced map preserves Coxeter length.
* `matrixHom_geometricAction`: coordinate inclusion intertwines the geometric actions.

## Implementation notes

The geometric action on the larger root space is a realization of the original Coxeter system.
Its proved faithfulness gives injectivity. Reduced parabolic words then prove length preservation.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.4 and 4.2.
-/

namespace BruhatIntervals

variable {Index Index' W W' : Type*} [Group W] [Group W']
  {matrix : CoxeterMatrix Index} {matrix' : CoxeterMatrix Index'}
  (cs : CoxeterSystem matrix W) (cs' : CoxeterSystem matrix' W')
  (index : Index → Index') (hentries : ∀ i j, matrix' (index i) (index j) = matrix i j)

include hentries in
private theorem index_relations (i j : Index) :
    (cs'.simple (index i) * cs'.simple (index j)) ^ matrix i j = 1 := by
  rw [← hentries]
  exact cs'.simple_mul_simple_pow (index i) (index j)

/-- The group homomorphism induced by a map preserving Coxeter-matrix entries. -/
noncomputable def matrixHom : W →* W' :=
  cs.lift ⟨fun i => cs'.simple (index i), index_relations cs' index hentries⟩

/-- The homomorphism sends a simple generator to its indexed simple generator. -/
theorem matrixHom_simple (i : Index) :
    matrixHom cs cs' index hentries (cs.simple i) = cs'.simple (index i) :=
  cs.lift_apply_simple (index_relations cs' index hentries) i

include hentries in
private theorem index_injective : Function.Injective index := by
  intro i j hij
  by_contra hne
  have h := hentries i j
  rw [hij, matrix'.diagonal] at h
  exact matrix.off_diagonal i j hne h.symm

private noncomputable def embeddingRealization : Realization cs (V := Index' →₀ ℝ) where
  simpleRoot := fun i => geometricRoot (index i)
  root_independent := geometricRoot_linearIndependent.comp index (index_injective index hentries)
  form := geometricForm matrix'
  form_isSymm := geometricForm_isSymm matrix'
  form_root := by
    intro i j
    rw [geometricForm_root, hentries]
  action := (geometricAction matrix' cs').comp (matrixHom cs cs' index hentries)
  action_simple := by
    intro i x
    rw [MonoidHom.comp_apply, matrixHom_simple, geometricAction_simple, geometricReflection_apply]

/-- A map preserving Coxeter-matrix entries induces an injective group map. -/
theorem matrixHom_injective : Function.Injective (matrixHom cs cs' index hentries) := by
  let realization := embeddingRealization cs cs' index hentries
  intro u v huv
  apply realization.action_injective
  change geometricAction matrix' cs' (matrixHom cs cs' index hentries u) =
    geometricAction matrix' cs' (matrixHom cs cs' index hentries v)
  rw [huv]

/-- The homomorphism evaluates a word by mapping each simple index. -/
theorem matrixHom_wordProd (word : List Index) :
    matrixHom cs cs' index hentries (cs.wordProd word) = cs'.wordProd (word.map index) := by
  induction word with
  | nil => rw [cs.wordProd_nil, map_one, List.map_nil, cs'.wordProd_nil]
  | cons i word ih =>
    rw [cs.wordProd_cons, map_mul, matrixHom_simple, ih, List.map_cons, cs'.wordProd_cons]

/-- The image is the standard parabolic subgroup on the image of the simple indices. -/
theorem matrixHom_range :
    (matrixHom cs cs' index hentries).range = cs'.parabolic (Set.range index) := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    apply cs.simple_induction_right w
    · rw [map_one]
      exact one_mem _
    · intro v i ih
      rw [map_mul, matrixHom_simple]
      exact mul_mem ih (cs'.simple_mem_parabolic ⟨i, rfl⟩)
  · apply cs'.parabolic_le_iff.mpr
    rintro j ⟨i, rfl⟩
    exact ⟨cs.simple i, matrixHom_simple cs cs' index hentries i⟩

private theorem exists_word_map {word : List Index'}
    (hletters : ∀ j ∈ word, j ∈ Set.range index) :
    ∃ old : List Index, old.map index = word := by
  induction word with
  | nil => exact ⟨[], rfl⟩
  | cons j word ih =>
    obtain ⟨i, hi⟩ := hletters j (by simp)
    obtain ⟨old, hmap⟩ := ih (fun k hk => hletters k (by simp [hk]))
    exact ⟨i :: old, by rw [List.map_cons, hmap, hi]⟩

/-- The induced group map preserves Coxeter length. -/
theorem matrixHom_length (w : W) :
    cs'.length (matrixHom cs cs' index hentries w) = cs.length w := by
  apply le_antisymm
  · obtain ⟨word, hred, rfl⟩ := cs.exists_isReduced w
    rw [matrixHom_wordProd]
    simpa only [List.length_map, ← hred.eq] using cs'.length_wordProd_le (word.map index)
  · have hmem : matrixHom cs cs' index hentries w ∈ cs'.parabolic (Set.range index) := by
      rw [← matrixHom_range cs cs' index hentries]
      exact ⟨w, rfl⟩
    obtain ⟨word, hred, hletters, hprod⟩ :=
      cs'.exists_isReduced_wordProd_eq_of_mem_parabolic hmem
    obtain ⟨old, hmap⟩ := exists_word_map index hletters
    have hwold : cs.wordProd old = w := matrixHom_injective cs cs' index hentries (by
      rw [matrixHom_wordProd, hmap, hprod])
    calc
      cs.length w = cs.length (cs.wordProd old) := congrArg cs.length hwold.symm
      _ ≤ old.length := cs.length_wordProd_le old
      _ = word.length := by simpa only [List.length_map] using congrArg List.length hmap
      _ = cs'.length (matrixHom cs cs' index hentries w) := by rw [← hprod, hred.eq]

private theorem root_map_linearCombination (x : Index →₀ ℝ) :
    Finsupp.linearCombination ℝ (fun i => geometricRoot (index i)) x =
      Finsupp.lmapDomain ℝ ℝ index x := by
  have hlinear : Finsupp.linearCombination ℝ (fun i => geometricRoot (index i)) =
      Finsupp.lmapDomain ℝ ℝ index := by
    apply Finsupp.lhom_ext
    intro i c
    simp only [Finsupp.linearCombination_single, geometricRoot, Finsupp.smul_single,
      smul_eq_mul, mul_one, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun hlinear x

/-- Inclusion of simple-root coordinates intertwines the geometric actions. -/
theorem matrixHom_geometricAction (w : W) (x : Index →₀ ℝ) :
    Finsupp.lmapDomain ℝ ℝ index (geometricAction matrix cs w x) =
      geometricAction matrix' cs' (matrixHom cs cs' index hentries w)
        (Finsupp.lmapDomain ℝ ℝ index x) := by
  have h := (embeddingRealization cs cs' index hentries).map_geometricAction w x
  change Finsupp.linearCombination ℝ (fun i => geometricRoot (index i))
      (geometricAction matrix cs w x) =
    geometricAction matrix' cs' (matrixHom cs cs' index hentries w)
      (Finsupp.linearCombination ℝ (fun i => geometricRoot (index i)) x) at h
  rwa [root_map_linearCombination, root_map_linearCombination] at h

end BruhatIntervals
