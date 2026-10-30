import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.AffineOpenMaps
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Principal Covers

Affine open immersions admit finite principal covers by localization isomorphisms.
-/

open CategoryTheory AlgebraicGeometry

namespace FrobeniusSplitting

universe u

/-- Affine open immersions are detected by finite principal covers and localized isomorphisms. -/
theorem isOpenImmersion_iff_away_maps {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) ↔
    ∃ (I : Type u) (_ : Finite I) (a : I → A),
      Ideal.span (Set.range (fun i ↦ f (a i))) = ⊤ ∧
        ∀ i, Function.Bijective (Localization.awayMap f (a i)) := by
  classical
  constructor
  · intro hopen
    let F := Spec.map (CommRingCat.ofHom f)
    have : IsOpenImmersion F := hopen
    let J := {a : A // PrimeSpectrum.basicOpen a ≤ F.opensRange}
    let W (j : J) := F ⁻¹ᵁ PrimeSpectrum.basicOpen j.val
    have hcover : (Set.univ : Set (Spec (.of B))) ⊆ ⋃ j : J, (W j : Set (Spec (.of B))) := by
      intro x _
      obtain ⟨V, ⟨a, rfl⟩, hxa, hV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        (PrimeSpectrum.isBasis_basic_opens (R := A))
        (show F x ∈ F.opensRange from ⟨x, rfl⟩)
      exact Set.mem_iUnion.mpr ⟨⟨a, hV⟩, hxa⟩
    have hcompact : IsCompact (Set.univ : Set (Spec (.of B))) := isCompact_univ
    obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover
      (fun j : J ↦ (W j : Set (Spec (.of B)))) (fun j ↦ (W j).isOpen) hcover
    refine ⟨t, inferInstance, (fun j ↦ j.val.val), ?_, fun j ↦ ?_⟩
    · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
      apply top_le_iff.mp
      intro x _
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (ht (show x ∈ Set.univ from trivial))
      obtain ⟨hjt, hx⟩ := Set.mem_iUnion.mp hj
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨j, hjt⟩, hx⟩
    · let V := PrimeSpectrum.basicOpen j.val.val
      have : IsOpenImmersion (F ∣_ V) :=
        IsZariskiLocalAtTarget.restrict (P := @IsOpenImmersion)
          (show IsOpenImmersion F from hopen) V
      have hiso : IsIso (F ∣_ V) := by
        apply isIso_of_isOpenImmersion_of_opensRange_eq_top
        apply top_le_iff.mp
        intro y _
        obtain ⟨x, hx⟩ := j.val.property y.property
        have hxi : x ∈ F ⁻¹ᵁ V := by
          change F x ∈ V
          rw [hx]
          exact y.property
        refine ⟨⟨x, hxi⟩, ?_⟩
        exact Subtype.ext ((morphismRestrict_base_coe F V ⟨x, hxi⟩).trans hx)
      have : IsIso (Spec.map (CommRingCat.ofHom (Localization.awayMap f j.val.val))) :=
        ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
          (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom f) j.val.val)).mp hiso
      exact (isIso_SpecMap_iff
        (f := CommRingCat.ofHom (Localization.awayMap f j.val.val))).mp inferInstance
  · rintro ⟨I, _, a, hcover, hlocal⟩
    exact isOpenImmersion_of_away_maps f a hcover hlocal

end FrobeniusSplitting
