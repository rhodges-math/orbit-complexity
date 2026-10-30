import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicProjection
import OrbitComplexity.ReductiveGroups.Roots.Inversions.PositiveRootConnectedSupport

/-!
# Parabolic Root Support

Positivity on the simple generators extends to every positive root
supported there. Applied to a minimum left parabolic representative,
this separates the parabolic positive roots from its left inversions. -/

namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

omit [P.IsReduced] in
/-- For these parameters,

```lean
b.IsPos (P.weylGroupToPerm w β)
```
-/
theorem isPos_weyl_image_of_simple_support (b : P.Base) (w : P.weylGroup)
    (J : Set b.support)
    (hJ : ∀ j ∈ J, b.IsPos (P.weylGroupToPerm w (j : ι)))
    (β : ι) (hβ : b.IsPos β) (hsupp : simpleRootSupportInt b β ⊆ J) :
    b.IsPos (P.weylGroupToPerm w β) := by
  have hprop : b.IsPos β ∧
      (simpleRootSupportInt b β ⊆ J → b.IsPos (P.weylGroupToPerm w β)) := by
    apply RootPairing.Base.IsPos.induction_on_add hβ
    · intro j hj
      refine ⟨b.isPos_of_mem_support hj, ?_⟩
      intro hs
      apply hJ ⟨j, hj⟩
      apply hs
      change simpleRootCoeffInt b j ⟨j, hj⟩ ≠ 0
      have hc : simpleRootCoeffInt b j ⟨j, hj⟩ = 1 := by
        simpa using simpleRootCoeffInt_simple b (⟨j, hj⟩ : b.support) ⟨j, hj⟩
      rw [hc]
      exact one_ne_zero
    · intro i j k hk hi hj
      refine ⟨hi.1.add (b.isPos_of_mem_support hj) hk, ?_⟩
      intro hs
      have he := simpleRootSupportInt_add_simple b hi.1 ⟨j, hj⟩ hk
      have hsi : simpleRootSupportInt b i ⊆ J := by
        intro a ha
        apply hs
        rw [he]
        exact Or.inl ha
      have hsj : (⟨j, hj⟩ : b.support) ∈ J := by
        apply hs
        rw [he]
        exact Or.inr rfl
      apply (hi.2 hsi).add (hJ ⟨j, hj⟩ hsj)
      simp only [← P.weylGroup_apply_root, hk, smul_add]
  exact hprop.2 hsupp

/-- For these parameters,

```lean
b.IsPos (P.weylGroupToPerm d⁻¹ β)
```
-/
theorem MinimalLeftParabolic.preserves_supported_positive_root
    (b : P.Base) (J : Set b.support) (d : P.weylGroup)
    (hd : IsMinimalLeftParabolic b J d) (β : ι)
    (hβ : b.IsPos β) (hsupp : simpleRootSupportInt b β ⊆ J) :
    b.IsPos (P.weylGroupToPerm d⁻¹ β) :=
  isPos_weyl_image_of_simple_support b d⁻¹ J
    ((isMinimalLeftParabolic_iff_isPos_inv b J d).mp hd) β hβ hsupp

/-- For these parameters,

```lean
β ∉ leftRootInversionIndices b d
```
-/
theorem ParabolicRootSupport.positive_root_not_left_inversion
    (b : P.Base) (J : Set b.support) (d : P.weylGroup)
    (hd : IsMinimalLeftParabolic b J d) (β : ι)
    (hβ : b.IsPos β) (hsupp : simpleRootSupportInt b β ⊆ J) :
    β ∉ leftRootInversionIndices b d := by
  intro hinv
  exact ((mem_leftRootInversionIndices b d β).mp hinv).2
    (MinimalLeftParabolic.preserves_supported_positive_root b J d hd β hβ hsupp)

end ReductiveGroups
