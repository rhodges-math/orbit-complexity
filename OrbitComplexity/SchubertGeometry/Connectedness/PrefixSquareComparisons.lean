import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixClosedSquares
import OrbitComplexity.FrobeniusSplitting.Normality.SchemeModels

set_option autoImplicit false

/-! # Scalar comparisons of mixed coordinate squares

Each affine comparison is used as a whole isomorphism over the coefficient
field. Its projection equation identifies a specified arithmetic arrow
with its prescribed arrow on coordinate rings.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u

private theorem comparison_natural {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} {U V : Over T}
    (EX : U ≅ Over.mk (pullback.fst κ X.hom))
    (EY : V ≅ Over.mk (pullback.fst κ Y.hom)) (f : X ⟶ Y) (g : U ⟶ V)
    (h : (EX.hom.left ≫ pullback.snd κ X.hom) ≫ f.left =
      g.left ≫ (EY.hom.left ≫ pullback.snd κ Y.hom)) :
    g.left ≫ EY.hom.left = EX.hom.left ≫ (chosenScalarArrow κ f).left := by
  apply pullback.hom_ext
  · calc
      (g.left ≫ EY.hom.left) ≫ pullback.fst κ Y.hom = g.left ≫ V.hom :=
        (Category.assoc _ _ _).trans (congrArg (fun k => g.left ≫ k) EY.hom.w)
      _ = U.hom := g.w
      _ = (EX.hom.left ≫ (chosenScalarArrow κ f).left) ≫ pullback.fst κ Y.hom :=
        (EX.hom.w).symm.trans
          ((congrArg (fun k => EX.hom.left ≫ k) (chosenScalarArrow κ f).w).symm.trans
            (Category.assoc _ _ _).symm)
  · calc
      (g.left ≫ EY.hom.left) ≫ pullback.snd κ Y.hom =
          (EX.hom.left ≫ pullback.snd κ X.hom) ≫ f.left :=
        (Category.assoc _ _ _).trans h.symm
      _ = EX.hom.left ≫ (pullback.snd κ X.hom ≫ f.left) := Category.assoc _ _ _
      _ = (EX.hom.left ≫ (chosenScalarArrow κ f).left) ≫ pullback.snd κ Y.hom :=
        (congrArg (fun k => EX.hom.left ≫ k) (chosenScalarArrow_snd κ f).symm).trans
          (Category.assoc _ _ _).symm

private def affine_scalar_iso {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (M : CommAlgCat.{u} R) (A : CommAlgCat.{u} K) (e : K ⊗[R] M ≃ₐ[K] A) :
    (algSpec (.of K)).obj (op A) ≅ Over.mk
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ((algSpec (.of R)).obj (op M)).hom) :=
  Over.isoMk (affineModelIso e) (affineModelIso_fst e)

private theorem affine_scalar_natural {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] {M N : CommAlgCat.{u} R} {A B : CommAlgCat.{u} K}
    (eM : K ⊗[R] M ≃ₐ[K] A) (eN : K ⊗[R] N ≃ₐ[K] B)
    (f₀ : M ⟶ N) (f : A ⟶ B)
    (hf : eN.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f₀.hom) =
      f.hom.comp eM.toAlgHom) :
    ((algSpec (.of K)).map f.op).left ≫ (affine_scalar_iso M A eM).hom.left =
      (affine_scalar_iso N B eN).hom.left ≫
        (chosenScalarArrow (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ((algSpec (.of R)).map f₀.op)).left := by
  let : Algebra R A := ((algebraMap K A).comp (algebraMap R K)).toAlgebra
  let : Algebra R B := ((algebraMap K B).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply comparison_natural _ (affine_scalar_iso N B eN) (affine_scalar_iso M A eM)
    ((algSpec (.of R)).map f₀.op) ((algSpec (.of K)).map f.op)
  change ((affineModelIso eN).hom ≫ pullback.snd _ _) ≫
      Spec.map (CommRingCat.ofHom f₀.hom.toRingHom) =
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
      ((affineModelIso eM).hom ≫ pullback.snd _ _)
  rw [affineModelIso_snd, affineModelIso_snd, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro m
  have hm := AlgHom.congr_fun hf ((1 : K) ⊗ₜ[R] m)
  change eN ((1 : K) ⊗ₜ[R] f₀.hom m) = f.hom (eM ((1 : K) ⊗ₜ[R] m)) at hm
  exact hm

/-- The prescribed tensor comparisons carry a Cartesian coordinate square
to the scalar extensions of its four specified arithmetic maps. -/
theorem prefix_model_cartesian {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (M₀ M₁ M₂ M₃ : CommAlgCat.{u} R)
    (A₀ A₁ A₂ A₃ : CommAlgCat.{u} K)
    (e₀ : K ⊗[R] M₀ ≃ₐ[K] A₀) (e₁ : K ⊗[R] M₁ ≃ₐ[K] A₁)
    (e₂ : K ⊗[R] M₂ ≃ₐ[K] A₂) (e₃ : K ⊗[R] M₃ ≃ₐ[K] A₃)
    (f₀ : M₀ ⟶ M₁) (g₀ : M₀ ⟶ M₂) (p₀ : M₁ ⟶ M₃) (q₀ : M₂ ⟶ M₃)
    (f : A₀ ⟶ A₁) (g : A₀ ⟶ A₂) (p : A₁ ⟶ A₃) (q : A₂ ⟶ A₃)
    (hf : e₁.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f₀.hom) =
      f.hom.comp e₀.toAlgHom)
    (hg : e₂.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K g₀.hom) =
      g.hom.comp e₀.toAlgHom)
    (hp : e₃.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K p₀.hom) =
      p.hom.comp e₁.toAlgHom)
    (hq : e₃.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K q₀.hom) =
      q.hom.comp e₂.toAlgHom)
    (h : IsPullback ((algSpec (.of K)).map p.op).left
      ((algSpec (.of K)).map q.op).left ((algSpec (.of K)).map f.op).left
      ((algSpec (.of K)).map g.op).left) :
    let κ := Spec.map (CommRingCat.ofHom (algebraMap R K))
    IsPullback (chosenScalarArrow κ ((algSpec (.of R)).map p₀.op)).left
      (chosenScalarArrow κ ((algSpec (.of R)).map q₀.op)).left
      (chosenScalarArrow κ ((algSpec (.of R)).map f₀.op)).left
      (chosenScalarArrow κ ((algSpec (.of R)).map g₀.op)).left :=
  h.of_iso ((Over.forget _).mapIso (affine_scalar_iso M₃ A₃ e₃))
    ((Over.forget _).mapIso (affine_scalar_iso M₁ A₁ e₁))
    ((Over.forget _).mapIso (affine_scalar_iso M₂ A₂ e₂))
    ((Over.forget _).mapIso (affine_scalar_iso M₀ A₀ e₀))
    (affine_scalar_natural e₁ e₃ p₀ p hp)
    (affine_scalar_natural e₂ e₃ q₀ q hq)
    (affine_scalar_natural e₀ e₁ f₀ f hf)
    (affine_scalar_natural e₀ e₂ g₀ g hg)

end SchubertGeometry
