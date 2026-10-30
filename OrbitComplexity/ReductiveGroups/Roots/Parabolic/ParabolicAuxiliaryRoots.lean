import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicSupportStability

/-!
# Parabolic Auxiliary Roots

the auxiliary roots a^{-1}(Phi_J^+ \ I_L(a)),
with subsystem membership expressed in the simple-root basis. -/

noncomputable section
namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- Positive parabolic roots not inverted by a, transported by
the inverse of a.  -/
def parabolicAuxiliaryRootIndices (b : P.Base) (J : Set b.support)
    (a : P.weylGroup) : Set ι :=
  P.weylGroupToPerm a⁻¹ ''
    {γ | b.IsPos γ ∧ simpleRootSupportInt b γ ⊆ J ∧
      γ ∉ leftRootInversionIndices b a}

omit [IsDomain R] [Finite ι] [P.IsReduced] [P.IsCrystallographic] in
/-- For these parameters,

```lean
b.IsPos β
```
-/
theorem parabolicAuxiliaryRootIndices_positive (b : P.Base)
    (J : Set b.support) (a : P.weylGroup) {β : ι}
    (hβ : β ∈ parabolicAuxiliaryRootIndices b J a) : b.IsPos β := by
  obtain ⟨γ, ⟨hγpos, _, hγnot⟩, rfl⟩ := hβ
  by_contra hn
  exact hγnot ((mem_leftRootInversionIndices b a γ).mpr ⟨hγpos, hn⟩)

/-- The inclusion is

```lean
simpleRootSupportInt b β ⊆ J
```
-/
theorem parabolicAuxiliaryRootIndices_support (b : P.Base)
    (J : Set b.support) (a : P.weylGroup)
    (ha : a ∈ standardParabolicSubgroup b J) {β : ι}
    (hβ : β ∈ parabolicAuxiliaryRootIndices b J a) :
    simpleRootSupportInt b β ⊆ J := by
  obtain ⟨γ, ⟨_, hγsupp, _⟩, rfl⟩ := hβ
  exact standardParabolic_preserves_root_support b J a⁻¹
    ((standardParabolicSubgroup b J).inv_mem ha) γ hγsupp

/-- The transported auxiliary set is disjoint from the inversion
set of any minimal left parabolic representative. -/
theorem ParabolicAuxiliaryRootIndices.disjoint_inversions (b : P.Base)
    (J : Set b.support) (a d : P.weylGroup)
    (ha : a ∈ standardParabolicSubgroup b J)
    (hd : IsMinimalLeftParabolic b J d) :
    Disjoint (parabolicAuxiliaryRootIndices b J a) (leftRootInversionIndices b d) := by
  apply Set.disjoint_left.mpr
  intro β hβA hβinv
  exact ParabolicRootSupport.positive_root_not_left_inversion b J d hd β
    (parabolicAuxiliaryRootIndices_positive b J a hβA)
    (parabolicAuxiliaryRootIndices_support b J a ha hβA) hβinv

end ReductiveGroups
