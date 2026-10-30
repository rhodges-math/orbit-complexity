import OrbitComplexity.GroupActions.Rosenlicht.RelationDimension

/-!
# Generators for fields of correspondences

If two copies of a field generate an extension, a generating tuple in one copy
generates the extension over the other copy. Polynomial relations in such a
tuple compute the extension's transcendence degree.
-/

open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w z

/-- A generating tuple in the second of two field images generates over the first image. -/
theorem adjoin_twoMaps_generators (K : Type u) [Field K]
    (F : Type v) [Field F] [Algebra K F]
    (L : Type w) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    (b : F →ₐ[K] L) {ι : Type z} (x : ι → F)
    (hx : IntermediateField.adjoin K (Set.range x) = ⊤)
    (hg : IntermediateField.adjoin K
      (Set.range (algebraMap F L) ∪ Set.range b) = ⊤) :
    IntermediateField.adjoin F (Set.range (fun i ↦ b (x i))) = ⊤ := by
  let E := IntermediateField.adjoin F (Set.range (fun i ↦ b (x i)))
  let C := E.restrictScalars K
  have hD : IntermediateField.adjoin K (Set.range x) ≤ C.comap b := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin F _ ⟨i, rfl⟩
  have hb (f : F) : b f ∈ E := hD (by rw [hx]; trivial)
  have hC : IntermediateField.adjoin K
      (Set.range (algebraMap F L) ∪ Set.range b) ≤ C := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z (⟨f, rfl⟩ | ⟨f, rfl⟩)
    · exact E.algebraMap_mem f
    · exact hb f
  rw [hg] at hC
  apply top_le_iff.mp
  intro z _
  exact hC trivial

/-- A field-generating tuple has a polynomial relation quotient of the field's
transcendence degree. -/
theorem relationQuotient_dim (F : Type u) [Field F]
    (L : Type v) [Field L] [Algebra F L] {ι : Type w} [Finite ι] (x : ι → L)
    (hx : IntermediateField.adjoin F (Set.range x) = ⊤) :
    ringKrullDim (MvPolynomial ι F ⧸ RingHom.ker
      (MvPolynomial.aeval x : MvPolynomial ι F →ₐ[F] L)) =
        (Algebra.trdeg F L).toNat := by
  let A := Algebra.adjoin F (Set.range x)
  let e := (Ideal.quotientKerEquivRange
    (MvPolynomial.aeval x : MvPolynomial ι F →ₐ[F] L)).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_range_eq_range_aeval F x).symm)
  have : IsFractionRing A L := adjoin_isFractionRing F x hx
  have : Algebra.FiniteType F A := Algebra.FiniteType.adjoin_of_finite (Set.finite_range x)
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  have hd := ringKrullDim_tensor_fraction F A L F
  rw [ringKrullDim_eq_of_ringEquiv (Algebra.TensorProduct.lid F A).toRingEquiv] at hd
  exact hd

end

end GroupActions
