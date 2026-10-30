import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Coordinates of affine patches in a scalar pullback -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u
namespace FrobeniusSplitting

/-- An affine scalar pullback has the tensor coordinate algebra, with both projection maps. -/
theorem exists_affine_scalar_coordinates {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] {X P : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of R)) (t : P ⟶ Spec (.of K)) (q : P ⟶ X)
    (h : IsPullback q t f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    letI : Algebra R Γ(X, ⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    letI : Algebra K Γ(P, ⊤) :=
      (t.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∃ e : K ⊗[R] Γ(X, ⊤) ≃ₐ[K] Γ(P, ⊤),
      (∀ k, e (k ⊗ₜ[R] (1 : Γ(X, ⊤))) = algebraMap K Γ(P, ⊤) k) ∧
      (∀ x, e ((1 : K) ⊗ₜ[R] x) = q.appTop.hom x) ∧
      ∀ k x, e (k ⊗ₜ[R] x) = algebraMap K Γ(P, ⊤) k * q.appTop.hom x := by
  let : Algebra R Γ(X, ⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let : Algebra K Γ(P, ⊤) :=
    (t.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  have H := (isPushout_appTop_of_isPullback h).flip
  have HP : IsPushout (CommRingCat.ofHom (algebraMap R K))
      (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap K Γ(P, ⊤))) q.appTop := by
    apply H.of_iso' (Scheme.ΓSpecIso (.of R)).symm
      (Scheme.ΓSpecIso (.of K)).symm (Iso.refl _) (Iso.refl _)
    · exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K))).symm
    · exact (Category.comp_id _).symm
    · exact (Category.comp_id _).symm
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  let HT := CommRingCat.isPushout_tensorProduct R K Γ(X, ⊤)
  let E := HT.isoIsPushout _ _ HP
  have hleft : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ E.hom =
      CommRingCat.ofHom (algebraMap K Γ(P, ⊤)) := HT.inl_isoIsPushout_hom _ _ HP
  have hright : CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ E.hom =
      q.appTop := HT.inr_isoIsPushout_hom _ _ HP
  let e : K ⊗[R] Γ(X, ⊤) ≃ₐ[K] Γ(P, ⊤) :=
    { E.commRingCatIsoToRingEquiv with
      commutes' := fun k ↦ congrArg (fun g : CommRingCat.of K ⟶ Γ(P, ⊤) ↦ g.hom k) hleft }
  have heL (k : K) : e (k ⊗ₜ[R] (1 : Γ(X, ⊤))) = algebraMap K Γ(P, ⊤) k := e.commutes k
  have heR (x : Γ(X, ⊤)) : e ((1 : K) ⊗ₜ[R] x) = q.appTop.hom x :=
    congrArg (fun g : CommRingCat.of Γ(X, ⊤) ⟶ Γ(P, ⊤) ↦ g.hom x) hright
  refine ⟨e, heL, heR, fun k x ↦ ?_⟩
  have H : e ((k ⊗ₜ[R] (1 : Γ(X, ⊤))) * ((1 : K) ⊗ₜ[R] x)) =
      e (k ⊗ₜ[R] (1 : Γ(X, ⊤))) * e ((1 : K) ⊗ₜ[R] x) := e.map_mul _ _
  simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, heL, heR] using H

end FrobeniusSplitting
