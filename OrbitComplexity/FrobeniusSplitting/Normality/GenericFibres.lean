import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Support
import Mathlib.Topology.Constructible
import Mathlib.Topology.Irreducible

/-!
# Generic vanishing from dense fibers

For a finite module over a finite-type algebra over a nontrivial Noetherian ring, vanishing on
a dense collection of base-prime quotients forces a nonzero element of the base to annihilate
the module. The proof uses the finite-module support and constructibility of its image in the
base spectrum. Over an integral base this gives vanishing after generic localization, and hence
surjectivity of localized linear maps whose cokernels vanish on dense fibers.
-/

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace Set

namespace FrobeniusSplitting

variable {X : Type*} [TopologicalSpace X]

private theorem open_subset_or_compl {S : Set X} (hS : IsConstructible S) :
    ∀ W : Set X, IsOpen W → W.Nonempty →
      ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ W ∧ (U ⊆ S ∨ U ⊆ Sᶜ) := by
  induction hS using IsConstructible.empty_union_induction with
  | open_retrocompact V hV _ =>
    intro W hW hWne
    by_cases hne : (W ∩ V).Nonempty
    · exact ⟨W ∩ V, hW.inter hV, hne, inter_subset_left, Or.inl inter_subset_right⟩
    · refine ⟨W, hW, hWne, Set.Subset.rfl, Or.inr ?_⟩
      intro x hxW hxV
      exact hne ⟨x, hxW, hxV⟩
  | union S _ T _ hS hT =>
    intro W hW hWne
    obtain ⟨U, hU, hUne, hUW, hUS | hUS⟩ := hS W hW hWne
    · exact ⟨U, hU, hUne, hUW, Or.inl (hUS.trans Set.subset_union_left)⟩
    obtain ⟨V, hV, hVne, hVU, hVT | hVT⟩ := hT U hU hUne
    · exact ⟨V, hV, hVne, hVU.trans hUW, Or.inl (hVT.trans Set.subset_union_right)⟩
    refine ⟨V, hV, hVne, hVU.trans hUW, Or.inr ?_⟩
    intro x hx hmem
    exact hmem.elim (hUS (hVU hx)) (hVT hx)
  | compl S _ hS =>
    intro W hW hWne
    obtain ⟨U, hU, hUne, hUW, hUS | hUS⟩ := hS W hW hWne
    · exact ⟨U, hU, hUne, hUW, Or.inr (by simpa only [compl_compl] using hUS)⟩
    · exact ⟨U, hU, hUne, hUW, Or.inl hUS⟩

/-- A dense constructible set in a nonempty space contains a nonempty open subset. -/
private theorem exists_open_subset [Nonempty X] {S : Set X}
    (hS : IsConstructible S) (hdense : Dense S) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ S := by
  obtain ⟨U, hU, hne, -, hUS | hUS⟩ :=
    open_subset_or_compl hS Set.univ isOpen_univ Set.univ_nonempty
  · exact ⟨U, hU, hne, hUS⟩
  · obtain ⟨x, hxS, hxU⟩ := hdense.exists_mem_open hU hne
    exact (hUS hxU hxS).elim


universe u v

/-- Vanishing of a finite module on dense base fibers forces a nonzero base element
into its annihilator. -/
theorem annihilator_meets_base {R A : Type u} {M : Type v} [CommRing R] [Nontrivial R]
    [IsNoetherianRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (D : Set (PrimeSpectrum R)) (hD : Dense D)
    (hz : ∀ p ∈ D, Subsingleton
      (M ⧸ ((p.asIdeal.map (algebraMap R A)) • ⊤ : Submodule A M))) :
    ∃ r : R, r ≠ 0 ∧ algebraMap R A r ∈ Module.annihilator A M := by
  classical
  let I := Module.annihilator A M
  by_contra hn
  have hI : I.comap (algebraMap R A) = ⊥ := by
    apply le_antisymm
    · intro r hr
      change r = 0
      by_contra hr0
      exact hn ⟨r, hr0, hr⟩
    · exact bot_le
  let φ := algebraMap R (A ⧸ I)
  have hker : RingHom.ker φ = ⊥ := by
    ext r
    change Ideal.Quotient.mk I (algebraMap R A r) = 0 ↔ r = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change r ∈ I.comap (algebraMap R A) ↔ r ∈ (⊥ : Ideal R)
    rw [hI]
  have hdense : DenseRange (PrimeSpectrum.comap φ) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mpr (hker ▸ bot_le)
  let g := Spec.map (CommRingCat.ofHom φ)
  have : LocallyOfFiniteType g :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hc : IsConstructible (Set.range (PrimeSpectrum.comap φ)) := by
    change IsConstructible (Set.range (g : Spec (.of (A ⧸ I)) → Spec (.of R)))
    simpa only [Set.image_univ] using g.isConstructible_image IsConstructible.univ
  obtain ⟨U, hU, hUne, hUr⟩ := exists_open_subset hc hdense
  obtain ⟨p, hpD, hpU⟩ := hD.exists_mem_open hU hUne
  obtain ⟨q, hq⟩ := hUr hpU
  let P := PrimeSpectrum.comap (Ideal.Quotient.mk I) q
  have hP : PrimeSpectrum.comap (algebraMap R A) P = p := hq
  have hIP : I ≤ P.asIdeal := by
    intro a ha
    change Ideal.Quotient.mk I a ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact q.asIdeal.zero_mem
  have hJP : p.asIdeal.map (algebraMap R A) ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (congrArg PrimeSpectrum.asIdeal hP).ge
  let N := M ⧸ ((p.asIdeal.map (algebraMap R A)) • ⊤ : Submodule A M)
  have : Subsingleton N := hz p hpD
  have hmem : P ∈ Module.support A N := by
    rw [Module.support_quotient]
    exact ⟨Module.mem_support_iff_of_finite.mpr hIP, hJP⟩
  rw [Module.support_eq_empty] at hmem
  exact hmem


/-- A finite module vanishing on dense fibers vanishes over the generic localization. -/
theorem subsingleton_of_dense_fibers {R A : Type u} {M : Type v}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] [AddCommGroup M]
    [Module A M] [Module R M] [IsScalarTower R A M] [Module.Finite A M]
    (D : Set (PrimeSpectrum R)) (hD : Dense D)
    (hz : ∀ p ∈ D, Subsingleton
      (M ⧸ ((p.asIdeal.map (algebraMap R A)) • ⊤ : Submodule A M))) :
    Subsingleton (LocalizedModule (nonZeroDivisors R) M) := by
  obtain ⟨r, hr, ha⟩ := annihilator_meets_base D hD hz
  apply LocalizedModule.subsingleton_iff.mpr
  intro m
  refine ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, ?_⟩
  rw [← IsScalarTower.algebraMap_smul A r m]
  exact Module.mem_annihilator.mp ha m

/-- Surjectivity on dense fibers implies surjectivity after generic localization. -/
theorem surjective_localizedMap_of_dense {R A : Type u} {M N : Type v}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [Module R M] [Module R N]
    [IsScalarTower R A M] [IsScalarTower R A N] [Module.Finite A N]
    (f : M →ₗ[A] N) (D : Set (PrimeSpectrum R)) (hD : Dense D)
    (hz : ∀ p ∈ D, Subsingleton
      ((N ⧸ f.range) ⧸
        ((p.asIdeal.map (algebraMap R A)) • ⊤ : Submodule A (N ⧸ f.range)))) :
    Function.Surjective (LocalizedModule.map (nonZeroDivisors R) (f.restrictScalars R)) := by
  apply (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker _ _).mpr
  change Subsingleton (LocalizedModule (nonZeroDivisors R) (N ⧸ f.range))
  exact subsingleton_of_dense_fibers D hD hz

end FrobeniusSplitting
