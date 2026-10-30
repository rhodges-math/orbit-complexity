import OrbitComplexity.BruhatIntervals.Graph.LongEdges
import OrbitComplexity.BruhatIntervals.Graph.Basic
import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.Systems

/-!
# Canonical rank-two systems on three-edge refinements

The three reflections in a directed three-edge refinement of a reflection edge have roots in
one plane. The canonical generators of their subgroup therefore construct a rank-two Coxeter
system, with its induced ambient Bruhat graph.

## Main results

* `long_edge_subsystem`: a three-edge refinement generates a canonical rank-two Coxeter system.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991),
  Lemma 3.1 and the proof of Proposition 3.3.
-/

namespace BruhatIntervals

variable {Index W : Type*} [Group W] {matrix : CoxeterMatrix Index}
  (cs : CoxeterSystem matrix W)

private theorem label_reflection {V : Type*} [AddCommGroup V] [Module ℝ V]
    (realization : Realization cs (V := V)) (x y : W) (h : (bruhatGraph cs).Adj x y) :
    (realization.rootReflection
      ⟨edgeLabel realization x y h, edgeLabel_positive realization x y h⟩).val = y * x⁻¹ := by
  have hright := congrArg (· * x⁻¹) (edgeLabel_target realization x y h)
  simpa only [mul_inv_cancel_right] using hright.symm

/-- The reflections of a directed three-edge refinement of a reflection edge generate a
rank-two Coxeter system whose simple generators are ambient canonical reflections. -/
theorem long_edge_subsystem (x a b y : W) (hxy : cs.BruhatStep x y)
    (hfirst : cs.BruhatStep x a) (hmiddle : cs.BruhatStep a b) (hlast : cs.BruhatStep b y) :
    let H := Subgroup.closure ({a * x⁻¹, b * a⁻¹, y * b⁻¹} : Set W)
    ∃ M : CoxeterMatrix Bool, ∃ system : CoxeterSystem M H,
      ∀ i : Bool, (system.simple i).val ∈ canonicalReflections cs H := by
  let realization := geometricRealization matrix cs
  let hxy' := (bruhatStep_iff_adj.mp hxy).1
  let hp := (bruhatStep_iff_adj.mp hfirst).1
  let hq := (bruhatStep_iff_adj.mp hmiddle).1
  let hr := (bruhatStep_iff_adj.mp hlast).1
  let α : {root : Index →₀ ℝ // root ∈ realization.positiveRoots} :=
    ⟨edgeLabel realization x y hxy', edgeLabel_positive realization x y hxy'⟩
  let β : {root : Index →₀ ℝ // root ∈ realization.positiveRoots} :=
    ⟨edgeLabel realization x a hp, edgeLabel_positive realization x a hp⟩
  let γ : {root : Index →₀ ℝ // root ∈ realization.positiveRoots} :=
    ⟨edgeLabel realization b y hr, edgeLabel_positive realization b y hr⟩
  let τ : {root : Index →₀ ℝ // root ∈ realization.positiveRoots} :=
    ⟨edgeLabel realization a b hq, edgeLabel_positive realization a b hq⟩
  have hp_twice : a * x⁻¹ * a = x := by
    have hself := hp.mul_self
    change (a * x⁻¹) * (a * x⁻¹) = 1 at hself
    have hright := congrArg (· * x) hself
    simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using hright
  have hprod : (realization.rootReflection α).val * (realization.rootReflection β).val =
      (realization.rootReflection γ).val * (realization.rootReflection τ).val := by
    dsimp only [α, β, γ, τ]
    rw [label_reflection, label_reflection, label_reflection, label_reflection]
    calc
      y * x⁻¹ * (a * x⁻¹) = y * (a⁻¹ * (a * x⁻¹ * a)) * x⁻¹ := by group
      _ = y * b⁻¹ * (b * a⁻¹) := by rw [hp_twice]; group
  have hne : (realization.rootReflection α).val * (realization.rootReflection β).val ≠ 1 := by
    dsimp only [α, β]
    rw [label_reflection, label_reflection]
    intro heq
    have hp_self := hp.mul_self
    change (a * x⁻¹) * (a * x⁻¹) = 1 at hp_self
    have heq' : y * x⁻¹ = a * x⁻¹ := mul_right_cancel (heq.trans hp_self.symm)
    have hya : y = a := mul_right_cancel heq'
    have hlt := hmiddle.length_lt.trans hlast.length_lt
    rw [hya] at hlt
    exact Nat.lt_irrefl _ hlt
  obtain ⟨hspan, hdim⟩ := realization.rootProduct_span α β γ τ hprod hne
  have hdistinct : β ≠ τ := by
    intro heq
    have href := congrArg (fun root => (realization.rootReflection root).val) heq
    change (realization.rootReflection
      ⟨edgeLabel realization x a hp, edgeLabel_positive realization x a hp⟩).val =
        (realization.rootReflection
          ⟨edgeLabel realization a b hq, edgeLabel_positive realization a b hq⟩).val at href
    rw [label_reflection, label_reflection] at href
    have hbx : b = x := by
      calc
        b = (b * a⁻¹) * a := by group
        _ = (a * x⁻¹) * a := by rw [← href]
        _ = x := hp_twice
    have hlt := hfirst.length_lt.trans hmiddle.length_lt
    rw [hbx] at hlt
    exact Nat.lt_irrefl _ hlt
  let plane := Submodule.span ℝ ({α.val, β.val} : Set (Index →₀ ℝ))
  have : FiniteDimensional ℝ plane := FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  let generators : Set {root : Index →₀ ℝ // root ∈ realization.positiveRoots} := {β, τ, γ}
  have hplane : ∀ root ∈ generators, root.val ∈ plane := by
    rintro root (rfl | rfl | rfl)
    · exact Submodule.subset_span (Or.inr rfl)
    · change τ.val ∈ Submodule.span ℝ ({α.val, β.val} : Set (Index →₀ ℝ))
      rw [hspan]
      exact Submodule.subset_span (Or.inr rfl)
    · change γ.val ∈ Submodule.span ℝ ({α.val, β.val} : Set (Index →₀ ℝ))
      rw [hspan]
      exact Submodule.subset_span (Or.inl rfl)
  have himage : ((fun root => (realization.rootReflection root).val) '' generators) =
      ({a * x⁻¹, b * a⁻¹, y * b⁻¹} : Set W) := by
    simp only [generators, Set.image_insert_eq, Set.image_singleton]
    dsimp only [β, τ, γ]
    rw [label_reflection, label_reflection, label_reflection]
  have hsystem := realization.reflection_closure_system plane hdim.le generators hplane
    ⟨β, Or.inl rfl, τ, Or.inr (Or.inl rfl), hdistinct⟩
  dsimp only at hsystem
  rw [himage] at hsystem
  exact hsystem

end BruhatIntervals
