import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.CellModelMaps
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.StageSections

/-! # Augmentation sections under an affine tensor comparison -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace SchubertGeometry.CellContraction
universe u

private theorem over_origin_compare {T : Type*} [Category T] {B D Y : T}
    (a : B ⟶ D) (b : Y ⟶ D) [HasPullback a b] (Z : Over B)
    (E : Over.mk (pullback.fst a b) ≅ Z)
    (s : B ⟶ pullback a b) (t : B ⟶ Z.left)
    (hs : s ≫ pullback.fst a b = 𝟙 B)
    (hq : s ≫ pullback.snd a b = t ≫ E.inv.left ≫ pullback.snd a b)
    (ht : t ≫ Z.hom = 𝟙 B) : s ≫ E.hom.left = t := by
  have hfst : s ≫ pullback.fst a b = (t ≫ E.inv.left) ≫ pullback.fst a b := by
    calc
      _ = 𝟙 B := hs
      _ = t ≫ Z.hom := ht.symm
      _ = t ≫ E.inv.left ≫ pullback.fst a b :=
        congrArg (fun f => t ≫ f) E.inv.w.symm
      _ = _ := (Category.assoc _ _ _).symm
  have he : s = t ≫ E.inv.left :=
    pullback.hom_ext hfst (by simpa only [Category.assoc] using hq)
  have hi : E.inv.left ≫ E.hom.left = 𝟙 Z.left := by
    simpa only [Over.comp_left, Over.id_left] using congrArg Over.Hom.left E.inv_hom_id
  rw [he, Category.assoc, hi, Category.comp_id]

private theorem augmentation_square
    {R K A C : Type u} [CommRing R] [CommRing K] [CommRing A] [CommRing C]
    [Algebra R K] [Algebra R A] [Algebra K C] [Algebra R C]
    (j : A →ₐ[R] C) (ε₀ : A →ₐ[R] R) (ε : C →ₐ[K] K)
    (h : ∀ a : A, algebraMap R K (ε₀ a) = ε (j a)) :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
        FrobeniusSplitting.algebraOriginSection ε₀ =
      FrobeniusSplitting.algebraOriginSection ε ≫ Spec.map (CommRingCat.ofHom j.toRingHom) := by
  have hRing : ε.toRingHom.comp j.toRingHom = (algebraMap R K).comp ε₀.toRingHom := by
    apply RingHom.ext
    intro a
    exact (h a).symm
  change Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
    Spec.map (CommRingCat.ofHom ε₀.toRingHom) =
      Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ Spec.map (CommRingCat.ofHom j.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg (fun f : A →+* K => Spec.map (CommRingCat.ofHom f)) hRing.symm

/-- A tensor comparison preserving the augmentation identifies its scalar section. -/
theorem affineOriginSection_comparison
    {K : Type u} [CommRing K] (R : Subalgebra ℤ K)
    {A C : Type u} [CommRing A] [CommRing C] [Algebra R A]
    [Algebra K C] [Algebra R C]
    (e : K ⊗[R] A ≃ₐ[K] C) (j : A →ₐ[R] C)
    (he : ∀ a : A, e ((1 : K) ⊗ₜ[R] a) = j a)
    (ε₀ : A →ₐ[R] R) (ε : C →ₐ[K] K)
    (hε : ∀ a : A, algebraMap R K (ε₀ a) = ε (j a)) :
    FrobeniusSplitting.genericOriginSection R
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (FrobeniusSplitting.algebraOriginSection ε₀)
        (FrobeniusSplitting.algebraOriginSection_base ε₀) ≫
        (tensorModelOverIso e).hom.left =
      FrobeniusSplitting.algebraOriginSection ε := by
  apply over_origin_compare
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) _ (tensorModelOverIso e)
  · exact FrobeniusSplitting.pullbackSection_base _ _ _ _
  · calc
      _ = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
          FrobeniusSplitting.algebraOriginSection ε₀ :=
        FrobeniusSplitting.pullbackSection_original _ _ _ _
      _ = FrobeniusSplitting.algebraOriginSection ε ≫
          Spec.map (CommRingCat.ofHom j.toRingHom) := augmentation_square j ε₀ ε hε
      _ = _ := congrArg (fun f => FrobeniusSplitting.algebraOriginSection ε ≫ f)
        (tensorModelOverIso_inv_snd e j he).symm
  · exact FrobeniusSplitting.algebraOriginSection_base ε

end SchubertGeometry.CellContraction
