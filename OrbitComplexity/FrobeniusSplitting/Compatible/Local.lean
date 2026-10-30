import OrbitComplexity.FrobeniusSplitting.Compatible.Schemes
import OrbitComplexity.FrobeniusSplitting.Compatible.Localization

/-!
# Compatibility on affine open covers

Compatibility with an ideal is preserved on principal opens by localization. A common principal
refinement of two affine charts then shows that compatibility with an ideal sheaf may be checked
on any affine open cover.
-/

namespace FrobeniusSplitting.SchemeSplitting

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X : Scheme} {p : ℕ}

/-- Compatibility on an affine open remains valid on each of its principal opens. -/
theorem compatible_basicOpen (splitting : SchemeSplitting X p) (ideal : X.IdealSheafData)
    (U : X.affineOpens) (f : Γ(X, U))
    (h : (splitting.onOpen U).IsCompatible (ideal.ideal U)) (hp : 0 < p) :
    (splitting.onOpen (X.basicOpen f)).IsCompatible
      (ideal.ideal (X.affineBasicOpen f)) := by
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  have heq := RingSplitting.localize_eq (S := Γ(X, X.basicOpen f)) (Submonoid.powers f)
    (splitting.onOpen U) hp (splitting.onOpen (X.basicOpen f))
    (fun a ↦ splitting.restrict_comm (X.basicOpen_le f) a)
  rw [← ideal.map_ideal_basicOpen U f, ← heq]
  exact h.localize (Submonoid.powers f) hp

/-- Compatibility of an ideal sheaf can be checked on an affine open cover. -/
theorem isCompatible_of_cover (splitting : SchemeSplitting X p) (ideal : X.IdealSheafData)
    (hp : 0 < p) {ι : Type*} (U : ι → X.affineOpens)
    (hU : ⨆ i, (U i).1 = ⊤)
    (H : ∀ i, (splitting.onOpen (U i)).IsCompatible (ideal.ideal (U i))) :
    splitting.IsCompatible ideal := by
  intro V a ha
  have hlocal : ∀ x : V.1, ∃ (i : ι) (r : Γ(X, V.1)) (rU : Γ(X, U i)),
      X.basicOpen r = X.basicOpen rU ∧ x.1 ∈ X.basicOpen r := by
    intro ⟨x, hxV⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    exact ⟨i, exists_basicOpen_le_affine_inter V.2 (U i).2 _ ⟨hxV, hi⟩⟩
  choose i r rU e hxr using hlocal
  have hspan : Ideal.span (Set.range r) = ⊤ := by
    rw [← V.2.self_le_iSup_basicOpen_iff]
    exact fun x hxV ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, _, rfl⟩, hxr ⟨x, hxV⟩⟩
  have inst := V.2.isLocalization_basicOpen
  refine Submodule.mem_of_isLocalized_span _ hspan (fun i ↦ Γ(X, X.basicOpen i.1))
    (fun i ↦ Algebra.linearMap Γ(X, V.1) Γ(X, X.basicOpen i.1)) ?_
  rintro ⟨_, j, rfl⟩
  simp only [← Submodule.restrictScalars_localized' Γ(X, X.basicOpen (r j)),
    Ideal.localized'_eq_map, RingHom.algebraMap_toAlgebra]
  erw [ideal.map_ideal (U := X.affineBasicOpen (r j)) (X.basicOpen_le (r j))]
  change X.presheaf.map (homOfLE (X.basicOpen_le (r j))).op
    (splitting.onOpen V a) ∈ ideal.ideal (X.affineBasicOpen (r j))
  rw [← splitting.restrict_comm]
  have hmem : X.presheaf.map (homOfLE (X.basicOpen_le (r j))).op a ∈
      ideal.ideal (X.affineBasicOpen (r j)) :=
    ideal.ideal_le_comap_ideal (X.basicOpen_le (r j)) ha
  have hc : (splitting.onOpen (X.basicOpen (r j))).IsCompatible
      (ideal.ideal (X.affineBasicOpen (r j))) := by
    have heq : X.affineBasicOpen (r j) = X.affineBasicOpen (rU j) := Subtype.ext (e j)
    change (splitting.onOpen (X.affineBasicOpen (r j)).1).IsCompatible _
    rw [heq]
    exact compatible_basicOpen splitting ideal (U (i j)) (rU j) (H (i j)) hp
  exact hc hmem

end FrobeniusSplitting.SchemeSplitting
