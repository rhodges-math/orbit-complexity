import OrbitComplexity.ReductiveGroups.Groups.Cells.BruhatDoubleCosets

/-! # The subgroup formed by Bruhat double cosets

Simple multiplication and inversion modulo the torus make the union a subgroup.
-/

namespace ReductiveGroups
noncomputable section

variable {ι R M₀ N₀ : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
  {P : RootPairing ι R M₀ N₀} [Finite ι] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced]
variable {Γ 𝕜 : Type*} [Group Γ] [Field 𝕜]
  {b : P.Base} {Bo T : Subgroup Γ} {f : ι → Γ} {Tr : Γ → Equiv.Perm ι → Prop}
  {x y : b.support → 𝕜 → Γ}

namespace IsBruhatSystem

private theorem mul_word (h : IsBruhatSystem b Bo T f Tr x y) :
    ∀ (l : List b.support) (a : Γ),
      (∃ v : P.weylGroup, a ∈ subgroupDoubleCoset Bo (weylElementPoint f b v)) →
        ∃ v : P.weylGroup,
          a * simpleWordPoint f b l ∈ subgroupDoubleCoset Bo (weylElementPoint f b v) := by
  intro l
  induction l with
  | nil =>
    intro a ha
    simpa only [simpleWordPoint_nil, mul_one] using ha
  | cons i l ih =>
    intro a ha
    obtain ⟨v, hv⟩ := ha
    have hn : ∃ w : P.weylGroup,
        a * f (i : ι) ∈ subgroupDoubleCoset Bo (weylElementPoint f b w) := by
      rcases h.doubleCoset_mul v i hv (mem_subgroupDoubleCoset_self Bo (f (i : ι))) with
        hvs | hv
      · exact ⟨v * RootPairing.weylGroup.ofIdx P (i : ι), hvs⟩
      · exact ⟨v, hv⟩
    simpa only [simpleWordPoint_cons, ← mul_assoc] using ih (a * f (i : ι)) hn

/-- The union of Bruhat double cosets is a subgroup. -/
def doubleCosetSubgroup (h : IsBruhatSystem b Bo T f Tr x y) : Subgroup Γ where
  carrier := {a | ∃ w : P.weylGroup,
    a ∈ subgroupDoubleCoset Bo (weylElementPoint f b w)}
  one_mem' := by
    refine ⟨1, ?_⟩
    rw [weylElementPoint_one]
    exact mem_subgroupDoubleCoset_self Bo 1
  mul_mem' := by
    intro a c ha hc
    obtain ⟨w, c₁, hc₁, c₂, hc₂, rfl⟩ := hc
    have hb : ∃ v : P.weylGroup,
        a * c₁ ∈ subgroupDoubleCoset Bo (weylElementPoint f b v) := by
      obtain ⟨v, hv⟩ := ha
      exact ⟨v, subgroupDoubleCoset_mul_mem hv hc₁⟩
    obtain ⟨v, hv⟩ := mul_word h (chosenReducedWord b w) (a * c₁) hb
    change (a * c₁) * weylElementPoint f b w ∈
      subgroupDoubleCoset Bo (weylElementPoint f b v) at hv
    refine ⟨v, ?_⟩
    simpa only [mul_assoc] using subgroupDoubleCoset_mul_mem hv hc₂
  inv_mem' := by
    intro a ha
    obtain ⟨w, c₁, hc₁, c₂, hc₂, rfl⟩ := ha
    obtain ⟨t, ht, he⟩ := h.weyl.weylElementPoint_inv b w
    refine ⟨w⁻¹, c₂⁻¹ * t, Bo.mul_mem (Bo.inv_mem hc₂) (h.torus_le ht),
      c₁⁻¹, Bo.inv_mem hc₁, ?_⟩
    simp only [mul_inv_rev, he]
    group

/-- The Borel subgroup lies in the union of Bruhat double cosets. -/
theorem borel_le_doubleCosetSubgroup (h : IsBruhatSystem b Bo T f Tr x y) :
    Bo ≤ h.doubleCosetSubgroup := by
  intro a ha
  refine ⟨1, a, ha, 1, Bo.one_mem, ?_⟩
  rw [weylElementPoint_one]
  group

end IsBruhatSystem
end
end ReductiveGroups