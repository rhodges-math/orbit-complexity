import OrbitComplexity.BruhatIntervals.Realizations.Extension
import OrbitComplexity.BruhatIntervals.Realizations.RootEmbedding
import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.Product

/-!
# Reflection products starting at a simple root

When the first root is simple, a different positive root has a nonzero coordinate at another
simple index. Two new Coxeter generators attached to those indices make the root-pairing
matrix nonsingular. The resulting common root plane and dihedral subgroup pull back through
the proved standard-parabolic embedding.

## Main results

* `rootProduct_simple`: a simple first root gives a common two-dimensional span and a dihedral
  subgroup for equal nonidentity reflection products.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991), Section 3.
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

private theorem exists_other_coordinate
    (α β : {x : Index →₀ ℝ // x ∈ (geometricRealization matrix cs).positiveRoots})
    (hne : α ≠ β) (i : Index) (hα : α.val = geometricRoot i) :
    ∃ j : Index, j ≠ i ∧ β.val j ≠ 0 := by
  classical
  by_contra hnot
  push Not at hnot
  have hcol : (β.val i) • α.val = β.val := by
    rw [hα]
    ext j
    by_cases hji : j = i
    · subst j
      simp only [geometricRoot, Finsupp.smul_apply, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    · simp only [geometricRoot, Finsupp.smul_apply, Finsupp.single_eq_of_ne hji,
        smul_eq_mul, mul_zero, hnot j hji]
  have hli := (geometricRealization matrix cs).positiveRoots_pair_independent β α hne.symm
  exact (linearIndependent_fin2.mp hli).2 (β.val i) hcol

/-- Equal nonidentity products starting at a simple root have the same two-dimensional root
span and generate a dihedral subgroup. -/
theorem rootProduct_simple
    (α β γ τ : {x : Index →₀ ℝ // x ∈ (geometricRealization matrix cs).positiveRoots})
    (i : Index) (hα : α.val = geometricRoot i)
    (hprod : ((geometricRealization matrix cs).rootReflection α).val *
        ((geometricRealization matrix cs).rootReflection β).val =
      ((geometricRealization matrix cs).rootReflection γ).val *
        ((geometricRealization matrix cs).rootReflection τ).val)
    (hne : ((geometricRealization matrix cs).rootReflection α).val *
      ((geometricRealization matrix cs).rootReflection β).val ≠ 1) :
    Submodule.span ℝ ({α.val, β.val} : Set (Index →₀ ℝ)) =
      Submodule.span ℝ ({γ.val, τ.val} : Set (Index →₀ ℝ)) ∧
    Module.finrank ℝ (Submodule.span ℝ ({α.val, β.val} : Set (Index →₀ ℝ))) = 2 ∧
    ∃ n : ℕ, Nonempty (DihedralGroup n ≃* Subgroup.closure
      ((fun root => ((geometricRealization matrix cs).rootReflection root).val) ''
        ({α, β, γ, τ} : Set {x : Index →₀ ℝ //
          x ∈ (geometricRealization matrix cs).positiveRoots}))) := by
  have hαβ : α ≠ β := by
    intro heq
    apply hne
    rw [heq]
    exact ((geometricRealization matrix cs).rootReflection β).property.mul_self
  obtain ⟨j, hji, hj⟩ := exists_other_coordinate cs α β hαβ i hα
  let extended := pairExtensionMatrix matrix i j
  let cs' := extended.toCoxeterSystem
  have hentries : ∀ k l, extended (Sum.inl k) (Sum.inl l) = matrix k l :=
    pairExtensionMatrix_old matrix i j
  let groupMap := matrixHom cs cs' Sum.inl hentries
  let rootMap := Finsupp.lmapDomain ℝ ℝ (Sum.inl : Index → Index ⊕ Bool)
  let realization := geometricRealization extended cs'
  let liftRoot (root : {x : Index →₀ ℝ //
      x ∈ (geometricRealization matrix cs).positiveRoots}) :
      {x : (Index ⊕ Bool) →₀ ℝ // x ∈ realization.positiveRoots} :=
    ⟨rootMap root.val, matrixHom_positiveRoot cs cs' Sum.inl hentries root.property⟩
  have hreflect (root : {x : Index →₀ ℝ //
      x ∈ (geometricRealization matrix cs).positiveRoots}) :
      (realization.rootReflection (liftRoot root)).val =
        groupMap ((geometricRealization matrix cs).rootReflection root).val :=
    matrixHom_rootReflection cs cs' Sum.inl hentries root
  have hprod' : (realization.rootReflection (liftRoot α)).val *
      (realization.rootReflection (liftRoot β)).val =
      (realization.rootReflection (liftRoot γ)).val *
        (realization.rootReflection (liftRoot τ)).val := by
    simp only [hreflect, ← map_mul, hprod]
  have hinjective : Function.Injective groupMap :=
    matrixHom_injective cs cs' Sum.inl hentries
  have hne' : (realization.rootReflection (liftRoot α)).val *
      (realization.rootReflection (liftRoot β)).val ≠ 1 := by
    intro heq
    apply hne
    apply hinjective
    simpa only [map_one, map_mul, ← hreflect] using heq
  let first := geometricRoot (Sum.inr false : Index ⊕ Bool)
  let second := geometricRoot (Sum.inr true : Index ⊕ Bool)
  have hdet : realization.form (liftRoot α).val first *
      realization.form (liftRoot β).val second -
      realization.form (liftRoot α).val second *
        realization.form (liftRoot β).val first ≠ 0 := by
    change geometricForm extended (rootMap α.val) first *
        geometricForm extended (rootMap β.val) second -
      geometricForm extended (rootMap α.val) second *
        geometricForm extended (rootMap β.val) first ≠ 0
    rw [hα]
    exact (pairExtension_pairing_det matrix i j β.val hji.symm) ▸ hj
  obtain ⟨hspan, _, n, ⟨equivalence⟩⟩ :=
    realization.rootProduct_plane (liftRoot α) (liftRoot β) (liftRoot γ) (liftRoot τ)
      hprod' hne' first second hdet
  have hrootInjective : Function.Injective rootMap :=
    Finsupp.mapDomain_injective Sum.inl_injective
  have hspan' : Submodule.span ℝ ({α.val, β.val} : Set (Index →₀ ℝ)) =
      Submodule.span ℝ ({γ.val, τ.val} : Set (Index →₀ ℝ)) := by
    apply Submodule.map_injective_of_injective hrootInjective
    rw [Submodule.map_span, Submodule.map_span, Set.image_pair, Set.image_pair]
    exact hspan
  refine ⟨hspan', (geometricRealization matrix cs).positiveRoots_pair_finrank α β hαβ, n, ?_⟩
  let originalRoots := ({α, β, γ, τ} : Set {x : Index →₀ ℝ //
    x ∈ (geometricRealization matrix cs).positiveRoots})
  let originalGroup := Subgroup.closure
    ((fun root => ((geometricRealization matrix cs).rootReflection root).val) '' originalRoots)
  have hgroupMap : originalGroup.map groupMap = Subgroup.closure
      ((fun root => (realization.rootReflection root).val) ''
        ({liftRoot α, liftRoot β, liftRoot γ, liftRoot τ} :
          Set {x : (Index ⊕ Bool) →₀ ℝ // x ∈ realization.positiveRoots})) := by
    dsimp only [originalGroup]
    rw [MonoidHom.map_closure]
    apply congrArg Subgroup.closure
    simp only [originalRoots, Set.image_insert_eq, Set.image_singleton, hreflect]
  exact ⟨equivalence.trans ((MulEquiv.subgroupCongr hgroupMap).symm.trans
    (originalGroup.equivMapOfInjective groupMap hinjective).symm)⟩

end BruhatIntervals
