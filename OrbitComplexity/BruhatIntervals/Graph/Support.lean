import OrbitComplexity.BruhatIntervals.Graph.CoverSpans
import OrbitComplexity.BruhatIntervals.Words.Support
import OrbitComplexity.BruhatIntervals.Realizations.Translate
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Support and lower interval spans

The covers of the identity are exactly the simple reflections. Their labels are the simple roots,
so the label span of a lower interval is the simple-root span of its support. Simple-root
independence identifies its algebraic dimension with the support cardinality.

## Main results

* `labelSpan_one`: a lower interval has the simple-root span of its support.
* `algebraicDim_one`: the algebraic dimension of a lower interval is its support cardinality.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 2.2 and 4.4.
-/

namespace BruhatIntervals

variable {Index W V : Type*} [Group W] {matrix : CoxeterMatrix Index}
  {cs : CoxeterSystem matrix W} [AddCommGroup V] [Module ℝ V]
  (realization : Realization cs (V := V))

private theorem simple_label (i : Index) (h : (bruhatGraph cs).Adj 1 (cs.simple i)) :
    edgeLabel realization 1 (cs.simple i) h = realization.simpleRoot i := by
  apply edgeLabel_unique realization h
    ⟨realization.simpleRoot i, realization.simpleRoot_mem_positiveRoots i⟩
  rw [realization.rootReflection_simple, mul_one]

/-- The label span of a lower interval is spanned by the simple roots in its support. -/
theorem labelSpan_one (w : W) :
    labelSpan realization 1 w = Submodule.span ℝ
      (realization.simpleRoot '' {i : Index | cs.BruhatLE (cs.simple i) w}) := by
  rw [(labelSpan_eq_covers realization 1 w (cs.one_bruhatLE w)).2.1]
  congr 1
  ext root
  constructor
  · rintro ⟨y, hy, hadj, hlength, rfl⟩
    have hlen : cs.length y = 1 := by simpa only [cs.length_one, zero_add] using hlength
    obtain ⟨i, rfl⟩ := cs.length_eq_one_iff.mp hlen
    exact ⟨i, hy.2, (simple_label realization i hadj).symm⟩
  · rintro ⟨i, hi, rfl⟩
    have hadj : (bruhatGraph cs).Adj 1 (cs.simple i) := by
      change cs.IsReflection (cs.simple i * (1 : W)⁻¹)
      simpa only [inv_one, mul_one] using cs.isReflection_simple i
    exact ⟨cs.simple i, ⟨cs.one_bruhatLE _, hi⟩, hadj,
      by simp only [cs.length_simple, cs.length_one, zero_add], simple_label realization i hadj⟩

/-- The algebraic dimension of a lower interval equals the cardinality of its support. -/
theorem algebraicDim_one (w : W) : algebraicDim realization 1 w = supportCard cs w := by
  classical
  let indices : Set Index := {i | cs.BruhatLE (cs.simple i) w}
  have himage : cs.simple '' indices = support cs w := by
    ext t
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, hi⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hi, rfl⟩
  have hfinite : indices.Finite :=
    Set.Finite.of_finite_image (himage ▸ support_finite cs w) (simple_injective cs).injOn
  let : Fintype indices := hfinite.fintype
  have hind : LinearIndependent ℝ (fun i : indices => realization.simpleRoot i.val) :=
    realization.root_independent.comp (fun i : indices => i.val) Subtype.val_injective
  have hrange : Set.range (fun i : indices => realization.simpleRoot i.val) =
      realization.simpleRoot '' indices := by
    ext root
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  calc
    algebraicDim realization 1 w = Module.finrank ℝ
        (Submodule.span ℝ (Set.range (fun i : indices => realization.simpleRoot i.val))) := by
      rw [algebraicDim, labelSpan_one, hrange]
    _ = Fintype.card indices := finrank_span_eq_card hind
    _ = indices.ncard := Set.fintypeCard_eq_ncard indices
    _ = supportCard cs w := by
      rw [supportCard, ← himage, Set.ncard_image_of_injective indices (simple_injective cs)]

end BruhatIntervals
