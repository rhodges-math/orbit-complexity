import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.Dihedral
import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.PairSystem

/-!
# Canonical Coxeter systems on planar reflection subgroups

Roots in a plane generate a subgroup with at most two canonical reflections. If two of the
generating roots are distinct, both canonical generators are present and distinct. The group
presentation of the pair constructs a Coxeter system with those canonical simple generators.

## Main results

* `Realization.reflection_closure_system`: a planar reflection subgroup with two distinct
  generating roots has a canonical rank-two Coxeter system.

## References

* M. Dyer, *Reflection Subgroups of Coxeter Systems*, Journal of Algebra 135 (1990),
  Sections 3 and 4.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]

private theorem reflection_ne_one {t : W} (ht : cs.IsReflection t) : t ≠ 1 := by
  intro heq
  have hpos := ht.odd_length.pos
  rw [heq, cs.length_one] at hpos
  omega

private theorem reflection_singleton {r t : W} (hr : cs.IsReflection r)
    (ht : cs.IsReflection t) (hmem : t ∈ Subgroup.closure ({r} : Set W)) : t = r := by
  rw [← Subgroup.zpowers_eq_closure] at hmem
  have horder : orderOf r = 2 := orderOf_eq_prime hr.pow_two (reflection_ne_one hr)
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two horder).mp hmem with hone | heq
  · exact (reflection_ne_one ht hone).elim
  · exact heq

private theorem pair_left_ne_one (H : Subgroup W) {r s a b : W}
    (hpair : H = Subgroup.closure ({r, s} : Set W))
    (hs : s = 1 ∨ cs.IsReflection s) (ha : a ∈ H) (hb : b ∈ H)
    (haref : cs.IsReflection a) (hbref : cs.IsReflection b) (hne : a ≠ b) : r ≠ 1 := by
  intro hr
  rw [hr, Subgroup.closure_insert_one] at hpair
  rcases hs with hone | href
  · rw [hone, Subgroup.closure_singleton_one] at hpair
    have haone : a = 1 := by simpa only [hpair, Subgroup.mem_bot] using ha
    exact reflection_ne_one haref haone
  · have ha' : a = s := reflection_singleton href haref (hpair ▸ ha)
    have hb' : b = s := reflection_singleton href hbref (hpair ▸ hb)
    exact hne (ha'.trans hb'.symm)

namespace Realization

variable (realization : Realization cs (V := V))

/-- A planar reflection subgroup containing two distinct generating roots has a Coxeter system
whose simple generators are its ambient canonical reflections. -/
theorem reflection_closure_system (plane : Submodule ℝ V) [FiniteDimensional ℝ plane]
    (hdim : Module.finrank ℝ plane ≤ 2)
    (generators : Set {x : V // x ∈ realization.positiveRoots})
    (hplane : ∀ root ∈ generators, root.val ∈ plane) (hnontrivial : generators.Nontrivial) :
    let H := Subgroup.closure
      ((fun root => (realization.rootReflection root).val) '' generators)
    ∃ M : CoxeterMatrix Bool, ∃ system : CoxeterSystem M H,
      ∀ i : Bool, (system.simple i).val ∈ canonicalReflections cs H := by
  classical
  let image := (fun root => (realization.rootReflection root).val) '' generators
  let H := Subgroup.closure image
  change ∃ M : CoxeterMatrix Bool, ∃ system : CoxeterSystem M H,
    ∀ i : Bool, (system.simple i).val ∈ canonicalReflections cs H
  obtain ⟨r, s, hr, hs, hpair⟩ :=
    realization.reflection_closure_pair plane hdim generators hplane
  change H = Subgroup.closure {r, s} at hpair
  obtain ⟨α, hα, β, hβ, hαβ⟩ := hnontrivial
  have hαH : (realization.rootReflection α).val ∈ H :=
    Subgroup.subset_closure ⟨α, hα, rfl⟩
  have hβH : (realization.rootReflection β).val ∈ H :=
    Subgroup.subset_closure ⟨β, hβ, rfl⟩
  have href : (realization.rootReflection α).val ≠ (realization.rootReflection β).val := by
    intro heq
    exact hαβ (realization.rootReflection_injective (Subtype.ext heq))
  have hrkind : r = 1 ∨ cs.IsReflection r := hr.imp_right And.left
  have hskind : s = 1 ∨ cs.IsReflection s := hs.imp_right And.left
  have hrne : r ≠ 1 := pair_left_ne_one H hpair hskind hαH hβH
    (realization.rootReflection α).property (realization.rootReflection β).property href
  have hsne : s ≠ 1 := by
    have hpair' : H = Subgroup.closure ({s, r} : Set W) := by rwa [Set.pair_comm]
    exact pair_left_ne_one H hpair' hrkind hαH hβH
      (realization.rootReflection α).property (realization.rootReflection β).property href
  have hrcan := hr.resolve_left hrne
  have hscan := hs.resolve_left hsne
  have hrs : r ≠ s := by
    intro heq
    have hsingle : H = Subgroup.closure ({r} : Set W) := by
      simpa [heq] using hpair
    have hαr := reflection_singleton hrcan.1
      (realization.rootReflection α).property (hsingle ▸ hαH)
    have hβr := reflection_singleton hrcan.1
      (realization.rootReflection β).property (hsingle ▸ hβH)
    exact href (hαr.trans hβr.symm)
  let rH : H := ⟨r, canonical_mem cs hrcan⟩
  let sH : H := ⟨s, canonical_mem cs hscan⟩
  have hrH : rH * rH = 1 := Subtype.ext hrcan.1.mul_self
  have hsH : sH * sH = 1 := Subtype.ext hscan.1.mul_self
  have hrHne : rH ≠ 1 := fun heq => hrne (congrArg Subtype.val heq)
  have hsHne : sH ≠ 1 := fun heq => hsne (congrArg Subtype.val heq)
  have hgen : Subgroup.closure ({rH, sH} : Set H) = ⊤ := by
    let K : Subgroup H := Subgroup.closure {rH, sH}
    have hle : H ≤ K.map H.subtype := by
      conv_lhs => rw [hpair]
      apply (Subgroup.closure_le _).mpr
      apply Set.pair_subset
      · exact ⟨rH, Subgroup.subset_closure (Or.inl rfl), rfl⟩
      · exact ⟨sH, Subgroup.subset_closure (Or.inr rfl), rfl⟩
    apply eq_top_iff.mpr
    intro g _
    obtain ⟨h, hh, heq⟩ := hle g.property
    exact (Subtype.ext heq : h = g) ▸ hh
  obtain ⟨M, system, hfalse, htrue, _⟩ := exists_pair_coxeter rH sH hrH hsH hrHne hsHne
    (fun heq => hrs (congrArg Subtype.val heq)) hgen
  refine ⟨M, system, ?_⟩
  intro i
  cases i
  · rw [hfalse]
    exact hrcan
  · rw [htrue]
    exact hscan

end Realization
end BruhatIntervals
