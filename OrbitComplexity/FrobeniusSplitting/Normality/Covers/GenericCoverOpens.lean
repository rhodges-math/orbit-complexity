import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Topology.Constructible
import Mathlib.Topology.Sober

/-! # Surjectivity near a generic point -/

open CategoryTheory AlgebraicGeometry Topology Set

namespace FrobeniusSplitting

private theorem constructible_generic_neighborhood {X : Type*} [TopologicalSpace X]
    {η : X} (hη : IsGenericPoint η Set.univ) {T : Set X} (hT : IsConstructible T) :
    ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ (U ⊆ T ∨ U ⊆ Tᶜ) := by
  classical
  induction hT using IsConstructible.empty_union_induction with
  | open_retrocompact V hV _ =>
    by_cases hηV : η ∈ V
    · exact ⟨V, hV, hηV, Or.inl Subset.rfl⟩
    · refine ⟨Set.univ, isOpen_univ, Set.mem_univ η, Or.inr ?_⟩
      intro x _ hx
      exact hηV ((hη.mem_open_set_iff hV).mpr ⟨x, Set.mem_univ x, hx⟩)
  | union T _ V _ hT hV =>
    obtain ⟨U, hU, hηU, hUT | hUT⟩ := hT
    · exact ⟨U, hU, hηU, Or.inl (hUT.trans Set.subset_union_left)⟩
    obtain ⟨W, hW, hηW, hWV | hWV⟩ := hV
    · exact ⟨W, hW, hηW, Or.inl (hWV.trans Set.subset_union_right)⟩
    refine ⟨U ∩ W, hU.inter hW, ⟨hηU, hηW⟩, Or.inr ?_⟩
    intro x hx hmem
    exact hmem.elim (hUT hx.1) (hWV hx.2)
  | compl T _ hT =>
    obtain ⟨U, hU, hηU, hUT | hUT⟩ := hT
    · exact ⟨U, hU, hηU, Or.inr (by simpa only [compl_compl] using hUT)⟩
    · exact ⟨U, hU, hηU, Or.inl hUT⟩

universe u

/-- Surjectivity over the generic point of an integral coefficient base extends
to a nonempty principal base open for morphisms of finite presentation. -/
theorem exists_surjective_base_open {R : Type u} [CommRing R] [IsDomain R]
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) (base : Y ⟶ Spec (.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    [LocallyOfFinitePresentation base] [QuasiCompact base]
    (hgeneric : ∀ y : Y, (base y).asIdeal = ⊥ → y ∈ Set.range f) :
    ∃ r : R, r ≠ 0 ∧
      ∀ y : Y, base y ∈ PrimeSpectrum.basicOpen r → y ∈ Set.range f := by
  let η : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  have hη : IsGenericPoint η Set.univ := by
    rw [isGenericPoint_def, PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  have hrange : IsConstructible (Set.range f) := by
    simpa only [Set.image_univ] using f.isConstructible_image IsConstructible.univ
  let T : Set (PrimeSpectrum R) := base '' (Set.range f)ᶜ
  have hT : IsConstructible T := base.isConstructible_image hrange.compl
  have hηT : η ∉ T := by
    rintro ⟨y, hy, hbase⟩
    exact hy (hgeneric y (congrArg PrimeSpectrum.asIdeal hbase))
  obtain ⟨U, hU, hηU, hUT | hUT⟩ := constructible_generic_neighborhood hη hT
  · exact (hηT (hUT hηU)).elim
  obtain ⟨_, ⟨r, rfl⟩, hηr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηU hU
  refine ⟨r, ?_, fun y hy ↦ ?_⟩
  · change r ∉ (⊥ : Ideal R) at hηr
    simpa only [Ideal.mem_bot] using hηr
  · by_contra hyf
    exact hUT (hrU hy) ⟨y, hyf, rfl⟩

end FrobeniusSplitting
