import OrbitComplexity.SchubertGeometry.LineBundles.Modules.AdjointGenerator

/-! # An adjoint chart map with a specified ambient inclusion -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open CategoryTheory
universe u v

/-- The adjoint chart construction has all section squares with the specified inclusion. -/
theorem adjointGenerator_embed
    {C : Type u} {D : Type v} [Category C] [Category D]
    {F : C ⥤ C} {H : C ⥤ D} {K : D ⥤ D} {P : D ⥤ C}
    {N : F ⋙ H ⟶ H ⋙ K} {O : C} {A : D}
    {r : H.obj O ⟶ A} {ua : F.obj O ⟶ O} {uf : K.obj A ⟶ A}
    (hu : N.app O ≫ K.map r ≫ uf = H.map ua ≫ r)
    (adj : H ⊣ P) {M : C} (v : H.obj M ⟶ A) (i : M ⟶ P.obj A)
    (hi : adj.homEquiv M A v = i) :
    ∃ q : F.obj M ⟶ P.obj A,
      ∀ (s t : O ⟶ M) (x y : A ⟶ A),
        H.map s ≫ v = r ≫ x → H.map t ≫ v = r ≫ y →
        K.map x ≫ uf = uf ≫ y → F.map s ≫ q = (ua ≫ t) ≫ i := by
  obtain ⟨q, hq⟩ := adjointGenerator_exists
    (C := C) (D := D) (F := F) (H := H) (K := K) (P := P)
    (N := N) (O := O) (A := A) (r := r) (ua := ua) (uf := uf) hu adj (M := M) v
  refine ⟨q, ?_⟩
  intro s t x y hs ht hx
  exact (hq s t x y hs ht hx).trans (congrArg (fun m => (ua ≫ t) ≫ m) hi)

end SchubertGeometry.ProjectiveLine
