import OrbitComplexity.ReductiveGroups.Roots.Inversions.AmbientInversions
import OrbitComplexity.ReductiveGroups.Roots.Supports.MinimalIrreducibleExpression

/-!
# Root Expression Auxiliary Occurrence

A distinct simple word has independent inversion roots. Thus a
different inversion root cannot be expressed using only distinguished
inversions; an admissible expression must contain an auxiliary occurrence.
Occurrences are retained in a multiset, including repeated root indices. -/

noncomputable section
namespace ReductiveGroups

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- A one-occurrence expression is its sole summand, so a root outside
`A ∪ D` has no one-occurrence admissible expression. -/
theorem RootExpression.card_ne_one_of_notMem_union
    {A D : Set ι} {β : ι} {s : Multiset ι}
    (hβ : β ∉ A ∪ D) (hs : RootExpression P A D β s) : s.card ≠ 1 := by
  intro hcard
  obtain ⟨γ, rfl⟩ := Multiset.card_eq_one.mp hcard
  have hγ : γ ∈ A ∨ γ ∈ D := hs.1 γ (by simp)
  have heq : γ = β := P.root.injective (by simpa [RootExpression] using hs.2)
  exact hβ (by simpa [heq] using hγ)

private theorem multiset_root_sum_mem_span
    (D : Set ι) (s : Multiset ι)
    (hs : ∀ γ ∈ s, γ ∈ D) :
    (s.map P.root).sum ∈ Submodule.span R (P.root '' D) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons γ s ih =>
      have hγ : γ ∈ D := hs γ (by simp)
      have hs' : ∀ δ ∈ s, δ ∈ D := by
        intro δ hδ
        exact hs δ (by simp [hδ])
      have hγspan : P.root γ ∈ Submodule.span R (P.root '' D) :=
        Submodule.subset_span ⟨γ, hγ, rfl⟩
      simpa using (Submodule.add_mem (Submodule.span R (P.root '' D))
        hγspan (ih hs'))

variable [CharZero R] [IsDomain R] [Finite ι]
  [P.IsCrystallographic] [P.IsReduced]

/-- If a target inversion of a distinct simple word is not among
the distinguished inversions, every admissible expression for it contains
an occurrence outside `D`. Minimality is unnecessary for this obstruction. -/
theorem RootExpression.RootExpressionAuxiliaryOccurrence.exists_occurrence_of_distinct_word
    (b : P.Base) (l : List b.support) (hl : l.Nodup)
    (A D : Set ι) (hD : D ⊆ leftRootInversionIndices b (simpleWeylWord b l))
    (β : ι) (hβ : β ∈ leftRootInversionIndices b (simpleWeylWord b l))
    (hβD : β ∉ D) (s : Multiset ι)
    (hs : RootExpression P A D β s) :
    ∃ γ ∈ s, γ ∉ D := by
  classical
  by_contra hnone
  push Not at hnone
  have hAll : ∀ γ ∈ s, γ ∈ D := by
    intro γ hγ
    exact hnone γ hγ
  let T : Set M := P.root '' D
  let V : Set M := leftRootInversions b (simpleWeylWord b l)
  have hTV : T ⊆ V := by
    change P.root '' D ⊆ P.root '' leftRootInversionIndices b (simpleWeylWord b l)
    exact Set.image_mono hD
  have hβV : P.root β ∈ V := ⟨β, hβ, rfl⟩
  have hlin : LinearIndepOn R id (insert (P.root β) T) := by
    exact (LeftRootInversions.simpleWeylWord_linearIndepOn_ambient b l hl).mono
      (Set.insert_subset hβV hTV)
  have hβT : P.root β ∉ T := by
    rintro ⟨γ, hγD, heq⟩
    have hγβ : γ = β := P.root.injective heq
    exact hβD (hγβ ▸ hγD)
  have hnotSpan : P.root β ∉ Submodule.span R T := by
    simpa using hlin.notMem_span_of_insert hβT
  have hsumMem : P.root β ∈ Submodule.span R T := by
    rw [← hs.2]
    exact multiset_root_sum_mem_span D s hAll
  exact hnotSpan hsumMem

end ReductiveGroups
