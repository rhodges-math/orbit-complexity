import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.GeometricProduct
import OrbitComplexity.BruhatIntervals.Realizations.Coordinates

/-!
# Root planes of equal reflection products

Equal nonidentity products of two reflections generate a dihedral reflection subgroup. Their
positive-root pairs span the same two-dimensional real subspace in every geometric realization.

## Main results

* `reflectionProduct_dihedral`: four reflections in an equal nonidentity pair product generate a
  dihedral subgroup.
* `Realization.rootProduct_span`: the two positive-root spans coincide and have dimension two.

## Implementation notes

The proof conjugates the first reflection to a simple reflection, constructs a Coxeter extension
with independent pairing functionals, and constructs canonical generators in its root plane.
The simple-root comparison map transports the resulting root-span equality to every realization.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991), Section 3.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W) [AddCommGroup V] [Module ℝ V]

/-- Four reflections with equal nonidentity pair products generate a dihedral subgroup. -/
theorem reflectionProduct_dihedral {a b c d : W}
    (ha : cs.IsReflection a) (hb : cs.IsReflection b)
    (hc : cs.IsReflection c) (hd : cs.IsReflection d)
    (hprod : a * b = c * d) (hne : a * b ≠ 1) :
    ∃ n : ℕ, Nonempty (DihedralGroup n ≃* Subgroup.closure ({a, b, c, d} : Set W)) := by
  let realization := geometricRealization matrix cs
  obtain ⟨α, hα⟩ := realization.rootReflection_surjective ⟨a, ha⟩
  obtain ⟨β, hβ⟩ := realization.rootReflection_surjective ⟨b, hb⟩
  obtain ⟨γ, hγ⟩ := realization.rootReflection_surjective ⟨c, hc⟩
  obtain ⟨τ, hτ⟩ := realization.rootReflection_surjective ⟨d, hd⟩
  have hαval := congrArg Subtype.val hα
  have hβval := congrArg Subtype.val hβ
  have hγval := congrArg Subtype.val hγ
  have hτval := congrArg Subtype.val hτ
  have hprod' : (realization.rootReflection α).val * (realization.rootReflection β).val =
      (realization.rootReflection γ).val * (realization.rootReflection τ).val := by
    simpa only [hαval, hβval, hγval, hτval] using hprod
  have hne' : (realization.rootReflection α).val * (realization.rootReflection β).val ≠ 1 := by
    simpa only [hαval, hβval] using hne
  obtain ⟨_, _, hdihedral⟩ := rootProduct_geometric cs α β γ τ hprod' hne'
  change ∃ n : ℕ, Nonempty (DihedralGroup n ≃* Subgroup.closure
    ({(realization.rootReflection α).val, (realization.rootReflection β).val,
      (realization.rootReflection γ).val, (realization.rootReflection τ).val} : Set W)) at hdihedral
  rw [hαval, hβval, hγval, hτval] at hdihedral
  exact hdihedral

namespace Realization

variable {cs} (realization : Realization cs (V := V))

/-- Equal nonidentity positive-root reflection products determine the same two-dimensional
real root span. -/
theorem rootProduct_span (α β γ τ : {x : V // x ∈ realization.positiveRoots})
    (hprod : (realization.rootReflection α).val * (realization.rootReflection β).val =
      (realization.rootReflection γ).val * (realization.rootReflection τ).val)
    (hne : (realization.rootReflection α).val * (realization.rootReflection β).val ≠ 1) :
    Submodule.span ℝ ({α.val, β.val} : Set V) = Submodule.span ℝ ({γ.val, τ.val} : Set V) ∧
      Module.finrank ℝ (Submodule.span ℝ ({α.val, β.val} : Set V)) = 2 := by
  let source := geometricRealization matrix cs
  let liftRoot (root : {x : V // x ∈ realization.positiveRoots}) :=
    source.rootReflectionEquiv.symm (realization.rootReflection root)
  have hreflection (root : {x : V // x ∈ realization.positiveRoots}) :
      (source.rootReflection (liftRoot root)).val = (realization.rootReflection root).val :=
    congrArg Subtype.val (source.rootReflectionEquiv.apply_symm_apply
      (realization.rootReflection root))
  have hmap (root : {x : V // x ∈ realization.positiveRoots}) :
      Finsupp.linearCombination ℝ realization.simpleRoot (liftRoot root).val = root.val :=
    realization.map_geometric_label root
  have hprod' : (source.rootReflection (liftRoot α)).val *
      (source.rootReflection (liftRoot β)).val =
      (source.rootReflection (liftRoot γ)).val * (source.rootReflection (liftRoot τ)).val := by
    simpa only [hreflection] using hprod
  have hne' : (source.rootReflection (liftRoot α)).val *
      (source.rootReflection (liftRoot β)).val ≠ 1 := by
    simpa only [hreflection] using hne
  obtain ⟨hspan, _, _⟩ := rootProduct_geometric cs
    (liftRoot α) (liftRoot β) (liftRoot γ) (liftRoot τ) hprod' hne'
  have hspan' := congrArg
    (Submodule.map (Finsupp.linearCombination ℝ realization.simpleRoot)) hspan
  rw [Submodule.map_span, Submodule.map_span, Set.image_pair, Set.image_pair,
    hmap, hmap, hmap, hmap] at hspan'
  refine ⟨hspan', realization.positiveRoots_pair_finrank α β ?_⟩
  intro heq
  apply hne
  rw [heq]
  exact (realization.rootReflection β).property.mul_self

end Realization
end BruhatIntervals
