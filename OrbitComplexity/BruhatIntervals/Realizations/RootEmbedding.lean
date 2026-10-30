import OrbitComplexity.BruhatIntervals.Realizations.Embedding
import OrbitComplexity.BruhatIntervals.Realizations.Coordinates

/-!
# Root labels under Coxeter embeddings

A map preserving Coxeter-matrix entries includes simple-root coordinates in the larger geometric
space. It preserves positive roots and their reflection labels, compatibly with the constructed
group embedding.

## Main results

* `matrixHom_positiveRoot`: coordinate inclusion sends positive roots to positive roots.
* `matrixHom_rootReflection`: the reflection label is transported by the group embedding.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991), Section 3.
-/

namespace BruhatIntervals

variable {Index Index' W W' : Type*} [Group W] [Group W']
  {matrix : CoxeterMatrix Index} {matrix' : CoxeterMatrix Index'}
  (cs : CoxeterSystem matrix W) (cs' : CoxeterSystem matrix' W')
  (index : Index → Index') (hentries : ∀ i j, matrix' (index i) (index j) = matrix i j)

include hentries

/-- Coordinate inclusion under a Coxeter-matrix embedding preserves positive roots. -/
theorem matrixHom_positiveRoot {x : Index →₀ ℝ}
    (hx : x ∈ (geometricRealization matrix cs).positiveRoots) :
    Finsupp.lmapDomain ℝ ℝ index x ∈ (geometricRealization matrix' cs').positiveRoots := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨w, i, hroot⟩ := hx.1
    refine ⟨matrixHom cs cs' index hentries w, index i, ?_⟩
    change geometricAction matrix' cs' (matrixHom cs cs' index hentries w)
      (geometricRoot (index i)) = Finsupp.lmapDomain ℝ ℝ index x
    change geometricAction matrix cs w (geometricRoot i) = x at hroot
    rw [← hroot, matrixHom_geometricAction cs cs' index hentries]
    simp only [geometricRoot, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  · rw [geometricCone_iff cs']
    intro j
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply, Finsupp.sum]
    apply Finset.sum_nonneg
    intro i _
    simp only [Finsupp.single_apply]
    split_ifs
    · exact (geometricCone_iff cs x).mp hx.2 i
    · exact le_rfl

/-- The reflection of an included positive root is the image of its original reflection. -/
theorem matrixHom_rootReflection
    (root : {x : Index →₀ ℝ // x ∈ (geometricRealization matrix cs).positiveRoots}) :
    ((geometricRealization matrix' cs').rootReflection
      ⟨Finsupp.lmapDomain ℝ ℝ index root.val,
        matrixHom_positiveRoot cs cs' index hentries root.property⟩).val =
      matrixHom cs cs' index hentries
        ((geometricRealization matrix cs).rootReflection root).val := by
  obtain ⟨w, i, hroot⟩ := root.property.1
  have hmap : Finsupp.lmapDomain ℝ ℝ index root.val =
      (geometricRealization matrix' cs').action (matrixHom cs cs' index hentries w)
        ((geometricRealization matrix' cs').simpleRoot (index i)) := by
    rw [← hroot]
    change Finsupp.lmapDomain ℝ ℝ index
      (geometricAction matrix cs w (geometricRoot i)) = _
    rw [matrixHom_geometricAction cs cs' index hentries]
    simp only [geometricRoot, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rfl
  have hpos : (geometricRealization matrix' cs').action
      (matrixHom cs cs' index hentries w)
      ((geometricRealization matrix' cs').simpleRoot (index i)) ∈
      (geometricRealization matrix' cs').positiveRoots := by
    rw [← hmap]
    exact matrixHom_positiveRoot cs cs' index hentries root.property
  have hsourcepos : (geometricRealization matrix cs).action w
      ((geometricRealization matrix cs).simpleRoot i) ∈
      (geometricRealization matrix cs).positiveRoots := hroot ▸ root.property
  have htarget :
      (⟨Finsupp.lmapDomain ℝ ℝ index root.val,
        matrixHom_positiveRoot cs cs' index hentries root.property⟩ :
          {x : Index' →₀ ℝ // x ∈ (geometricRealization matrix' cs').positiveRoots}) =
        ⟨(geometricRealization matrix' cs').action (matrixHom cs cs' index hentries w)
          ((geometricRealization matrix' cs').simpleRoot (index i)), hpos⟩ := Subtype.ext hmap
  have hsource : root =
      ⟨(geometricRealization matrix cs).action w
        ((geometricRealization matrix cs).simpleRoot i), hsourcepos⟩ := Subtype.ext hroot.symm
  rw [htarget, (geometricRealization matrix' cs').rootReflection_translated_simple,
    hsource, (geometricRealization matrix cs).rootReflection_translated_simple,
    map_mul, map_mul, map_inv, matrixHom_simple]

end BruhatIntervals
