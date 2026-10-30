import OrbitComplexity.BruhatIntervals.Graph.Forks
import OrbitComplexity.BruhatIntervals.Graph.ToricMaxima
import OrbitComplexity.BruhatIntervals.Graph.Diamonds

/-!
# Interval properties for arbitrary Coxeter systems

The labelled graph definitions, root-product spans, diamond and long-edge configurations,
interval span recurrences, dimension bounds, and attained toric maxima hold for every Coxeter
system and every geometric realization. The statements impose no finiteness hypothesis on the
group or its simple index type.

## Main results

* `coxeter_interval_properties`: the complete collection of universal interval properties.

## References

* M. Dyer, *On the Bruhat Graph of a Coxeter System*, Compositio Mathematica 78 (1991).
* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005).
-/

namespace BruhatIntervals

/-- The labelled Bruhat graph and all interval span, diamond, dimension, and toric properties
hold for arbitrary Coxeter systems and geometric realizations. -/
theorem coxeter_interval_properties :
  (∀ {S : Type*} {W : Type*} {V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V)) (u v : W),
    cs.BruhatLE u v →
    (∀ x y : W, (bruhatGraph cs).Adj x y ↔
      ∃ root : {α : V // α ∈ realization.positiveRoots},
        y = (realization.rootReflection root).val * x) ∧
    (∀ (x y : W) (h : (bruhatGraph cs).Adj x y),
      edgeLabel realization x y h ∈ realization.positiveRoots ∧
      y = (realization.rootReflection
        ⟨edgeLabel realization x y h, edgeLabel_positive realization x y h⟩).val * x ∧
      edgeLabel realization x y h =
        edgeLabel realization y x ((bruhatGraph cs).adj_symm h)) ∧
    (∀ x y : bruhatInterval cs u v,
      (intervalGraph (cs := cs) u v).Adj x y ↔ (bruhatGraph cs).Adj x.val y.val)
  ) ∧
  (∀ {S : Type*} {W : Type*} {V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V)) (u v : W),
    cs.BruhatLE u v →
    labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ y ∈ bruhatInterval cs u v,
        ∃ h : (bruhatGraph cs).Adj x y, edgeLabel realization x y h = α} ∧
    labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ x y : W, cs.BruhatLE u x ∧ cs.BruhatLE y v ∧
        ∃ h : (bruhatGraph cs).Adj x y, cs.length x < cs.length y ∧
          edgeLabel realization x y h = α} ∧
    FiniteDimensional ℝ (labelSpan realization u v) ∧
    algebraicDim realization u v = Module.finrank ℝ (labelSpan realization u v)
  ) ∧
  (∀ {S : Type*} {W : Type*} {V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V))
    (α β γ τ : {x : V // x ∈ realization.positiveRoots}),
    (realization.rootReflection α).val * (realization.rootReflection β).val =
      (realization.rootReflection γ).val * (realization.rootReflection τ).val →
    (realization.rootReflection α).val * (realization.rootReflection β).val ≠ 1 →
    Submodule.span ℝ ({α.val, β.val} : Set V) =
      Submodule.span ℝ ({γ.val, τ.val} : Set V) ∧
    Module.finrank ℝ (Submodule.span ℝ ({α.val, β.val} : Set V)) = 2
  ) ∧
  (∀ {S : Type*} {W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (x y : W),
    cs.BruhatStep x y → cs.length x + 1 < cs.length y →
    ∃ a b c d : W, a ∈ bruhatInterval cs x y ∧ b ∈ bruhatInterval cs x y ∧
      c ∈ bruhatInterval cs x y ∧ d ∈ bruhatInterval cs x y ∧ a ≠ b ∧ c ≠ d ∧
      (bruhatGraph cs).Adj x a ∧ (bruhatGraph cs).Adj x b ∧
      (bruhatGraph cs).Adj a c ∧ (bruhatGraph cs).Adj a d ∧
      (bruhatGraph cs).Adj b c ∧ (bruhatGraph cs).Adj b d ∧
      (bruhatGraph cs).Adj c y ∧ (bruhatGraph cs).Adj d y
  ) ∧
  (∀ {S : Type*} {W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    (w t : W) (i : S), cs.IsReflection t →
    letI : PartialOrder W := cs.bruhatPartialOrder
    ((w * cs.simple i ⋖ w) → (t * w ⋖ w) → w * cs.simple i ≠ t * w →
      (t * w * cs.simple i ⋖ w * cs.simple i) ∧ (t * w * cs.simple i ⋖ t * w)) ∧
    ((w ⋖ w * cs.simple i) → (w ⋖ t * w) → w * cs.simple i ≠ t * w →
      (w * cs.simple i ⋖ t * w * cs.simple i) ∧ (t * w ⋖ t * w * cs.simple i))
  ) ∧
  (∀ {S : Type*} {W : Type*} {V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V)) (u v : W),
    cs.BruhatLE u v →
    labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ y ∈ bruhatInterval cs u v,
        ∃ h : (bruhatGraph cs).Adj x y, cs.length y = cs.length x + 1 ∧
          edgeLabel realization x y h = α} ∧
    labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ y ∈ bruhatInterval cs u v, ∃ h : (bruhatGraph cs).Adj u y,
        cs.length y = cs.length u + 1 ∧ edgeLabel realization u y h = α} ∧
    labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ h : (bruhatGraph cs).Adj x v,
        cs.length v = cs.length x + 1 ∧ edgeLabel realization x v h = α}
  ) ∧
  (∀ {S : Type*} {W : Type*} {V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V)) (u v : W),
    cs.BruhatLE u v → ∀ i : S, cs.IsRightDescent v i →
    (cs.IsRightDescent u i →
      labelSpan realization u v = labelSpan realization (u * cs.simple i) (v * cs.simple i)) ∧
    (¬ cs.IsRightDescent u i →
      labelSpan realization u v = labelSpan realization u (v * cs.simple i) ⊔
        Submodule.span ℝ ({(edgeLabel realization u (u * cs.simple i)
          ((cs.isReflection_simple i).conj u))} : Set V))
  ) ∧
  (∀ {S : Type*} {W : Type*} {V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V)) (u v : W),
    cs.BruhatLE u v →
    (∀ w ∈ bruhatInterval cs u v, ∀ h : (bruhatGraph cs).Adj w v,
      cs.length v = cs.length w + 1 →
        labelSpan realization u v = labelSpan realization u w ⊔
          Submodule.span ℝ ({(edgeLabel realization w v h)} : Set V)) ∧
    (∀ vertices : List W,
      vertices.head? = some u → vertices.getLast? = some v →
      vertices.IsChain (fun x y => cs.BruhatLE x y ∧ cs.length y = cs.length x + 1) →
      labelSpan realization u v = Submodule.span ℝ
        {α : V | ∃ x y : W, (x, y) ∈ vertices.zip vertices.tail ∧
          ∃ h : (bruhatGraph cs).Adj x y, edgeLabel realization x y h = α}) ∧
    (∀ w ∈ bruhatInterval cs u v, labelSpan realization u v = Submodule.span ℝ
      {α : V | ∃ x ∈ bruhatInterval cs u v, ∃ h : (bruhatGraph cs).Adj w x,
        (cs.length x = cs.length w + 1 ∨ cs.length w = cs.length x + 1) ∧
          edgeLabel realization w x h = α})
  ) ∧
  (∀ {S : Type*} {W : Type*} {V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V)) (u v : W),
    cs.BruhatLE u v →
    algebraicDim realization u v ≤ cs.length v - cs.length u ∧
    (IsToricInterval realization u v ↔ algebraicDim realization u v = cs.length v - cs.length u)

  ) ∧
  (∀ {S : Type*} {W : Type*} {V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V)) (u v : W),
    cs.BruhatLE u v →
    IsGreatest {n : ℕ | ∃ w ∈ bruhatInterval cs u v,
      IsToricInterval realization u w ∧ cs.length w - cs.length u = n}
      (algebraicDim realization u v) ∧
    IsGreatest {n : ℕ | ∃ w ∈ bruhatInterval cs u v,
      IsToricInterval realization w v ∧ cs.length v - cs.length w = n}
      (algebraicDim realization u v) ∧
    IsGreatest {n : ℕ | ∃ x ∈ bruhatInterval cs u v, ∃ y ∈ bruhatInterval cs u v,
      cs.BruhatLE x y ∧ IsToricInterval realization x y ∧ cs.length y - cs.length x = n}
      (algebraicDim realization u v)
  ) ∧
  (∀ {S : Type*} {W : Type*} {V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V))
    (u v x y1 y2 : W), cs.BruhatLE u v →
    x ∈ bruhatInterval cs u v → y1 ∈ bruhatInterval cs u v →
    y2 ∈ bruhatInterval cs u v → y1 ≠ y2 →
    let : PartialOrder W := cs.bruhatPartialOrder
    x ⋖ y1 → y1 ⋖ v → x ⋖ y2 → y2 ⋖ v →
    algebraicDim realization u v - algebraicDim realization u x = 1 →
    labelSpan realization u v = labelSpan realization u y1 ∨
      labelSpan realization u v = labelSpan realization u y2
  ) := by
  refine ⟨bruhat_graph_definitions, algebraic_dim_definitions,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S W V _ M cs _ _ realization
    exact realization.rootProduct_span
  · intro S W _ M cs
    exact long_edge_fork cs
  · intro S W _ M cs
    exact strong_weak_diamond cs
  · intro S W V _ M cs _ _ realization
    exact labelSpan_eq_covers realization
  · intro S W V _ M cs _ _ realization
    exact labelSpan_recursion realization
  · intro S W V _ M cs _ _ realization
    exact labelSpan_properties realization
  · intro S W V _ M cs _ _ realization
    exact toric_interval_definition realization
  · intro S W V _ M cs _ _ realization
    exact toric_interval_maxima realization
  · intro S W V _ M cs _ _ realization
    exact swap_zero_one realization

end BruhatIntervals
