import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.SimpleProduct
import OrbitComplexity.BruhatIntervals.Realizations.Translate

/-!
# Reflection products in the geometric realization

Conjugating the first reflection to a simple reflection reduces equal nonidentity reflection
products to the simple-root case. Positive sign representatives preserve the two root spans,
and conjugation transports the constructed dihedral subgroup back to the original subgroup.

## Main results

* `rootProduct_geometric`: equal nonidentity geometric root products have equal two-dimensional
  spans and generate a dihedral reflection subgroup.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991), Section 3.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W) [AddCommGroup V] [Module ℝ V]

private theorem span_pair_signs {x y x' y' : V} (hx : x' = x ∨ x' = -x)
    (hy : y' = y ∨ y' = -y) :
    Submodule.span ℝ ({x', y'} : Set V) = Submodule.span ℝ ({x, y} : Set V) := by
  have mem_of_sign {z z' : V} (h : z' = z ∨ z' = -z)
      (plane : Submodule ℝ V) (hz : z ∈ plane) : z' ∈ plane := by
    rcases h with rfl | rfl
    · exact hz
    · exact plane.neg_mem hz
  have reverse_sign {z z' : V} (h : z' = z ∨ z' = -z) : z = z' ∨ z = -z' := by
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (neg_neg z).symm
  apply le_antisymm
  · apply Submodule.span_le.mpr
    exact Set.pair_subset (mem_of_sign hx _ (Submodule.subset_span (Or.inl rfl)))
      (mem_of_sign hy _ (Submodule.subset_span (Or.inr rfl)))
  · apply Submodule.span_le.mpr
    exact Set.pair_subset (mem_of_sign (reverse_sign hx) _ (Submodule.subset_span (Or.inl rfl)))
      (mem_of_sign (reverse_sign hy) _ (Submodule.subset_span (Or.inr rfl)))

/-- Equal nonidentity reflection products in the canonical geometric realization have equal
two-dimensional spans and generate a dihedral subgroup. -/
theorem rootProduct_geometric
    (α β γ τ : {x : Index →₀ ℝ // x ∈ (geometricRealization matrix cs).positiveRoots})
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
      ({((geometricRealization matrix cs).rootReflection α).val,
        ((geometricRealization matrix cs).rootReflection β).val,
        ((geometricRealization matrix cs).rootReflection γ).val,
        ((geometricRealization matrix cs).rootReflection τ).val} : Set W)) := by
  let realization := geometricRealization matrix cs
  obtain ⟨w, i, hα⟩ := α.property.1
  let α' : {x : Index →₀ ℝ // x ∈ realization.positiveRoots} :=
    ⟨realization.simpleRoot i, realization.simpleRoot_mem_positiveRoots i⟩
  have hαimage : realization.action (w⁻¹) α.val = α'.val := by
    change realization.action (w⁻¹) α.val = realization.simpleRoot i
    rw [← hα, realization.action_inv_action]
  have hαpos : realization.action (w⁻¹) α.val ∈ realization.positiveRoots :=
    hαimage ▸ α'.property
  have hαref := realization.rootReflection_conj (w⁻¹) α hαpos
  have hαsub : (⟨realization.action (w⁻¹) α.val, hαpos⟩ :
      {x : Index →₀ ℝ // x ∈ realization.positiveRoots}) = α' := Subtype.ext hαimage
  rw [hαsub, inv_inv] at hαref
  obtain ⟨β', hβsign, hβref⟩ := realization.exists_positive_translate (w⁻¹) β
  obtain ⟨γ', hγsign, hγref⟩ := realization.exists_positive_translate (w⁻¹) γ
  obtain ⟨τ', hτsign, hτref⟩ := realization.exists_positive_translate (w⁻¹) τ
  simp only [inv_inv] at hβref hγref hτref
  have hprod' : (realization.rootReflection α').val * (realization.rootReflection β').val =
      (realization.rootReflection γ').val * (realization.rootReflection τ').val := by
    rw [hαref, hβref, hγref, hτref]
    calc
      _ = w⁻¹ * ((realization.rootReflection α).val *
          (realization.rootReflection β).val) * w := by group
      _ = w⁻¹ * ((realization.rootReflection γ).val *
          (realization.rootReflection τ).val) * w := by rw [hprod]
      _ = _ := by group
  have hne' : (realization.rootReflection α').val * (realization.rootReflection β').val ≠ 1 := by
    intro heq
    apply hne
    have hback : w * ((realization.rootReflection α').val *
        (realization.rootReflection β').val) * w⁻¹ =
        (realization.rootReflection α).val * (realization.rootReflection β).val := by
      rw [hαref, hβref]
      group
    rw [← hback, heq, mul_one, mul_inv_cancel]
  obtain ⟨hspan, _, n, ⟨equivalence⟩⟩ := rootProduct_simple cs α' β' γ' τ' i rfl hprod' hne'
  have hfirst : Submodule.span ℝ ({α'.val, β'.val} : Set (Index →₀ ℝ)) =
      (Submodule.span ℝ ({α.val, β.val} : Set (Index →₀ ℝ))).map
        (realization.action (w⁻¹)).toLinearMap := by
    rw [Submodule.map_span, Set.image_pair]
    exact span_pair_signs (Or.inl hαimage.symm) hβsign
  have hsecond : Submodule.span ℝ ({γ'.val, τ'.val} : Set (Index →₀ ℝ)) =
      (Submodule.span ℝ ({γ.val, τ.val} : Set (Index →₀ ℝ))).map
        (realization.action (w⁻¹)).toLinearMap := by
    rw [Submodule.map_span, Set.image_pair]
    exact span_pair_signs hγsign hτsign
  have hspan' : Submodule.span ℝ ({α.val, β.val} : Set (Index →₀ ℝ)) =
      Submodule.span ℝ ({γ.val, τ.val} : Set (Index →₀ ℝ)) := by
    apply Submodule.map_injective_of_injective (realization.action (w⁻¹)).injective
    rw [← hfirst, ← hsecond]
    exact hspan
  have hαβ : α ≠ β := by
    intro heq
    apply hne
    rw [heq]
    exact (realization.rootReflection β).property.mul_self
  refine ⟨hspan', realization.positiveRoots_pair_finrank α β hαβ, n, ?_⟩
  let originalGroup := Subgroup.closure
    ({(realization.rootReflection α).val, (realization.rootReflection β).val,
      (realization.rootReflection γ).val, (realization.rootReflection τ).val} : Set W)
  let translatedGroup := Subgroup.closure
    ({(realization.rootReflection α').val, (realization.rootReflection β').val,
      (realization.rootReflection γ').val, (realization.rootReflection τ').val} : Set W)
  let conjugation := MulAut.conj (w⁻¹)
  have hgroupMap : originalGroup.map conjugation.toMonoidHom = translatedGroup := by
    dsimp only [originalGroup]
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton]
    change Subgroup.closure
      ({w⁻¹ * (realization.rootReflection α).val * (w⁻¹)⁻¹,
        w⁻¹ * (realization.rootReflection β).val * (w⁻¹)⁻¹,
        w⁻¹ * (realization.rootReflection γ).val * (w⁻¹)⁻¹,
        w⁻¹ * (realization.rootReflection τ).val * (w⁻¹)⁻¹} : Set W) = translatedGroup
    simp only [inv_inv, ← hαref, ← hβref, ← hγref, ← hτref]
    rfl
  have hgroupEq : Subgroup.closure
      ((fun root => (realization.rootReflection root).val) ''
        ({α', β', γ', τ'} : Set {x : Index →₀ ℝ // x ∈ realization.positiveRoots})) =
      translatedGroup := by
    simp only [Set.image_insert_eq, Set.image_singleton]
    rfl
  exact ⟨equivalence.trans ((MulEquiv.subgroupCongr hgroupEq).trans
    ((MulEquiv.subgroupCongr hgroupMap).symm.trans
      (originalGroup.equivMapOfInjective conjugation.toMonoidHom conjugation.injective).symm))⟩

end BruhatIntervals
