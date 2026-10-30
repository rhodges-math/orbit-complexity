import OrbitComplexity.ReductiveGroups.Lie.Exponential.MatrixNilpotentAdjoint
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralRadicalCartanNilpotent
import Mathlib.Algebra.Lie.Engel

/-!
# Jordan Cartan Criterion

A conditional internal Cartan criterion from Jordan parts.
It is applied to the torus of a reductive group in
`Groups/TorusCentralizerJordan.lean`; the geometric input is verified in
`Groups/MaximalTorusLieCartan.lean`. -/

noncomputable section
namespace ReductiveGroups

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K L A : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [Ring A] [Algebra K A]

omit [CharZero K] in
/-- If each element of a self-normalizing subalgebra splits into an
associatively nilpotent part in the subalgebra and a part centralizing it,
Engel's theorem makes the subalgebra Cartan. -/
theorem jordan_isCartanSubalgebra
    (T H : LieSubalgebra K L) (_hTH : T ≤ H)
    (hcentral : ∀ t : L, t ∈ T → ∀ y : L, y ∈ H → ⁅t, y⁆ = 0)
    (hnorm : H.normalizer = H)
    (f : L →ₗ⁅K⁆ A) (hf : Function.Injective f)
    (hparts : ∀ x : H, ∃ xn : H, ∃ xs : T,
      (xn : L) + (xs : L) = (x : L) ∧ IsNilpotent (f (xn : L))) :
    H.IsCartanSubalgebra := by
  have hnil : LieRing.IsNilpotent H := by
    apply (LieAlgebra.isNilpotent_iff_forall (R := K) (L := H)).mpr
    intro x
    obtain ⟨xn, xs, hsum, hxn⟩ := hparts x
    have hnad : IsNilpotent (LieAlgebra.ad K H xn) :=
      LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad H
        (MatrixNilpotentAdjoint.ad_injective_associative_representation
          f hf (xn : L) hxn)
    have hxad : LieAlgebra.ad K H x = LieAlgebra.ad K H xn := by
      ext y
      change ⁅(x : L), (y : L)⁆ = ⁅(xn : L), (y : L)⁆
      have hxy := congrArg (fun z : L => ⁅z, (y : L)⁆) hsum
      rw [add_lie, hcentral (xs : L) xs.property (y : L) y.property,
        add_zero] at hxy
      exact hxy.symm
    rw [hxad]
    exact hnad
  exact ⟨hnil, hnorm⟩

/-- In a central-radical Lie algebra, the same Jordan condition forces
equality with the chosen centralizing subalgebra when central nilpotents
vanish in the faithful representation. -/
theorem JordanCartanCriterion.cartans_equal_of_no_central_nilpotents
    [LieAlgebra.HasCentralRadical K L]
    (T H : LieSubalgebra K L) (hTH : T ≤ H)
    (hcentral : ∀ t : L, t ∈ T → ∀ y : L, y ∈ H → ⁅t, y⁆ = 0)
    (hnorm : H.normalizer = H)
    (f : L →ₗ⁅K⁆ A) (hf : Function.Injective f)
    (hparts : ∀ x : H, ∃ xn : H, ∃ xs : T,
      (xn : L) + (xs : L) = (x : L) ∧ IsNilpotent (f (xn : L)))
    (hzero : ∀ z : L, z ∈ LieAlgebra.center K L →
      IsNilpotent (f z) → z = 0) :
    H = T := by
  have hcartan : H.IsCartanSubalgebra :=
    jordan_isCartanSubalgebra T H hTH hcentral hnorm f hf hparts
  apply le_antisymm
  · intro x hx
    obtain ⟨xn, xs, hsum, hxn⟩ := hparts ⟨x, hx⟩
    have hnad : IsNilpotent (LieAlgebra.ad K L (xn : L)) :=
      MatrixNilpotentAdjoint.ad_injective_associative_representation f hf (xn : L) hxn
    have hcenter : (xn : L) ∈ LieAlgebra.center K L :=
      @CentralRadical.cartan_nilpotent_ad_mem_center K L _ _ _ _ _ _
        H hcartan (xn : L) xn.property hnad
    have hxn0 : (xn : L) = 0 := hzero (xn : L) hcenter hxn
    have hxs : (xs : L) = x := by simpa only [hxn0, zero_add] using hsum
    exact hxs ▸ xs.property
  · exact hTH

end ReductiveGroups
