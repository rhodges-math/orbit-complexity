import Batteries.Tactic.OpenPrivate
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixSquareComparisons
import OrbitComplexity.FrobeniusSplitting.Normality.AffinePushouts
import Mathlib.RingTheory.FiniteStability
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

set_option autoImplicit false

/-! # Scalar extension of coordinate functors and their spectrum squares

Tensor extension carries the coefficient diagram and its morphisms.
Affine pullback isomorphisms identify the extended spectrum maps with
the scalar pullback maps and retain their Cartesian squares.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u v w

open private scalar_functor scalar_preserves_limit scalar_arrow_cartesian
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendCellConnected
open private affine_scalar_iso affine_scalar_natural
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixSquareComparisons
open private inner_square
  from OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian

private theorem identity_square {A B T : Type u} [CommRing A] [CommRing B]
    [CommRing T] [Algebra T A] [Algebra T B] (f g : A →ₐ[T] B) (h : f = g) :
    (AlgEquiv.refl : B ≃ₐ[T] B).toAlgHom.comp f =
      g.comp (AlgEquiv.refl : A ≃ₐ[T] A).toAlgHom := by
  subst g
  rfl

variable (S R : Type u) [CommRing S] [CommRing R] [Algebra S R]

private def tensor_functor : CommAlgCat.{u} S ⥤ CommAlgCat.{u} R where
  obj M := CommAlgCat.of R (R ⊗[S] M)
  map f := CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := R) R f.hom)
  map_id _ := CommAlgCat.hom_ext Algebra.TensorProduct.map_id
  map_comp f g := CommAlgCat.hom_ext (Algebra.TensorProduct.map_id_comp g.hom f.hom)

private theorem tensor_map_hom {M N : CommAlgCat.{u} S} (f : M ⟶ N) :
    ((tensor_functor S R).map f).hom =
      Algebra.TensorProduct.lTensor (S := R) R f.hom := rfl

private theorem cancel_natural {K : Type u} [CommRing K]
    [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    {M N : CommAlgCat.{u} S} (f : M ⟶ N) :
    (Algebra.TensorProduct.cancelBaseChange S R K K N).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (R := R) (S := K) K
        (Algebra.TensorProduct.lTensor (S := R) R f.hom)) =
      (Algebra.TensorProduct.lTensor (S := K) K f.hom).comp
        (Algebra.TensorProduct.cancelBaseChange S R K K M).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro k x
  induction x using TensorProduct.inductionOn with
  | tmul r m =>
      change Algebra.TensorProduct.cancelBaseChange S R K K N
          (k ⊗ₜ[R] (r ⊗ₜ[S] f.hom m)) =
        (Algebra.TensorProduct.lTensor (S := K) K f.hom)
          (Algebra.TensorProduct.cancelBaseChange S R K K M (k ⊗ₜ[R] (r ⊗ₜ[S] m)))
      rw [Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.TensorProduct.cancelBaseChange_tmul]
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add, AlgHom.comp_apply] using congrArg₂ (· + ·) hx hy

private def tensor_comparison {K : Type u} [CommRing K]
    [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    (M : CommAlgCat.{u} S) (A : CommAlgCat.{u} K) (e : K ⊗[S] M ≃ₐ[K] A) :
    K ⊗[R] (tensor_functor S R).obj M ≃ₐ[K] A :=
  (Algebra.TensorProduct.cancelBaseChange S R K K M).trans e

private theorem tensor_comparison_natural {K : Type u} [CommRing K]
    [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    {M N : CommAlgCat.{u} S} {A B : CommAlgCat.{u} K}
    (eM : K ⊗[S] M ≃ₐ[K] A) (eN : K ⊗[S] N ≃ₐ[K] B)
    (f₀ : M ⟶ N) (f : A ⟶ B)
    (h : eN.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K f₀.hom) =
      f.hom.comp eM.toAlgHom) :
    (tensor_comparison S R N B eN).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (R := R) (S := K) K
        ((tensor_functor S R).map f₀).hom) =
      f.hom.comp (tensor_comparison S R M A eM).toAlgHom := by
  apply AlgHom.ext
  intro x
  exact (congrArg eN (AlgHom.congr_fun (cancel_natural S R f₀) x)).trans
    (AlgHom.congr_fun h (Algebra.TensorProduct.cancelBaseChange S R K K M x))

private theorem tensor_comparison_original {K : Type u} [CommRing K]
    [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    (M : CommAlgCat.{u} S) (A : CommAlgCat.{u} K) (e : K ⊗[S] M ≃ₐ[K] A)
    (k : K) (m : M) :
    tensor_comparison S R M A e (k ⊗ₜ[R] ((1 : R) ⊗ₜ[S] m)) = e (k ⊗ₜ[S] m) := by
  change e (Algebra.TensorProduct.cancelBaseChange S R K K M
    (k ⊗ₜ[R] ((1 : R) ⊗ₜ[S] m))) = e (k ⊗ₜ[S] m)
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]

private theorem tensor_surjective_later {K : Type u} [CommRing K]
    [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    {M N : CommAlgCat.{u} S} (f : M ⟶ N)
    (h : Function.Surjective (Algebra.TensorProduct.lTensor (S := R) R f.hom)) :
    Function.Surjective (Algebra.TensorProduct.lTensor (S := K) K f.hom) := by
  have hK : Function.Surjective
      (Algebra.TensorProduct.lTensor (R := R) (S := K) K
        (Algebra.TensorProduct.lTensor (S := R) R f.hom)) :=
    Algebra.TensorProduct.map_surjective (AlgHom.id K K)
      (Algebra.TensorProduct.lTensor (S := R) R f.hom) (fun x => ⟨x, rfl⟩) h
  intro b
  obtain ⟨x, hx⟩ := hK ((Algebra.TensorProduct.cancelBaseChange S R K K N).symm b)
  refine ⟨Algebra.TensorProduct.cancelBaseChange S R K K M x, ?_⟩
  exact (AlgHom.congr_fun (cancel_natural S R f) x).symm.trans
    ((congrArg (Algebra.TensorProduct.cancelBaseChange S R K K N) hx).trans
      ((Algebra.TensorProduct.cancelBaseChange S R K K N).apply_symm_apply b))

private def scalar_spec_comparison
    (F : CommAlgCat.{u} S ⥤ CommAlgCat.{u} R)
    (e : ∀ M : CommAlgCat.{u} S, R ⊗[S] M ≃ₐ[R] F.obj M)
    (he : ∀ {M N : CommAlgCat.{u} S} (f : M ⟶ N), (e N).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := R) R f.hom) =
      (F.map f).hom.comp (e M).toAlgHom) :
    F.op ⋙ algSpec (.of R) ≅
      algSpec (.of S) ⋙ scalar_functor (Spec.map (CommRingCat.ofHom (algebraMap S R))) :=
  NatIso.ofComponents
    (fun M => affine_scalar_iso M.unop (F.obj M.unop) (e M.unop))
    (fun {M N} f => by
      apply (Over.forget (Spec (.of R))).map_injective
      exact affine_scalar_natural (e N.unop) (e M.unop) f.unop (F.map f.unop) (he f.unop))

private def tensor_spec_iso :
    (tensor_functor S R).op ⋙ algSpec (.of R) ≅
      algSpec (.of S) ⋙ scalar_functor (Spec.map (CommRingCat.ofHom (algebraMap S R))) :=
  scalar_spec_comparison S R (tensor_functor S R)
    (fun M => (AlgEquiv.refl : R ⊗[S] M ≃ₐ[R] R ⊗[S] M))
    (fun f => identity_square (Algebra.TensorProduct.lTensor (S := R) R f.hom)
      (((tensor_functor S R).map f).hom) (tensor_map_hom S R f).symm)

private theorem tensor_open {M N : CommAlgCat.{u} S} (f : M ⟶ N)
    [IsOpenImmersion ((algSpec (.of S)).map f.op).left] :
    IsOpenImmersion ((algSpec (.of R)).map ((tensor_functor S R).map f).op).left := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let E := tensor_spec_iso S R
  have hscalar : IsOpenImmersion (chosenScalarArrow κ ((algSpec (.of S)).map f.op)).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (scalar_arrow_cartesian κ ((algSpec (.of S)).map f.op)).flip inferInstance
  let h := Arrow.isoMk
    (f := Arrow.mk (((algSpec (.of R)).map ((tensor_functor S R).map f).op).left))
    (g := Arrow.mk ((chosenScalarArrow κ ((algSpec (.of S)).map f.op)).left))
    ((Over.forget _).mapIso (E.app (op N)))
    ((Over.forget _).mapIso (E.app (op M)))
    (congrArg (fun a => a.left) (E.hom.naturality f.op)).symm
  exact (MorphismProperty.arrow_mk_iso_iff (@IsOpenImmersion) h).mpr hscalar

private theorem tensor_pushout {M₀ M₁ M₂ M₃ : CommAlgCat.{u} S}
    (f : M₀ ⟶ M₁) (g : M₀ ⟶ M₂) (p : M₁ ⟶ M₃) (q : M₂ ⟶ M₃)
    (h : IsPushout (CommRingCat.ofHom f.hom.toRingHom)
      (CommRingCat.ofHom g.hom.toRingHom) (CommRingCat.ofHom p.hom.toRingHom)
      (CommRingCat.ofHom q.hom.toRingHom)) :
    IsPushout (CommRingCat.ofHom ((tensor_functor S R).map f).hom.toRingHom)
      (CommRingCat.ofHom ((tensor_functor S R).map g).hom.toRingHom)
      (CommRingCat.ofHom ((tensor_functor S R).map p).hom.toRingHom)
      (CommRingCat.ofHom ((tensor_functor S R).map q).hom.toRingHom) := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let E := tensor_spec_iso S R
  have hS : IsPullback ((algSpec (.of S)).map p.op) ((algSpec (.of S)).map q.op)
      ((algSpec (.of S)).map f.op) ((algSpec (.of S)).map g.op) :=
    IsPullback.of_map_of_faithful (Over.forget _)
      ((isPushout_iff_spec_pullback _ _ _ _).mp h)
  have hR := (hS.map (scalar_functor κ)).map (Over.forget _)
  have hnew : IsPullback
      (((tensor_functor S R).op ⋙ algSpec (.of R)).map p.op).left
      (((tensor_functor S R).op ⋙ algSpec (.of R)).map q.op).left
      (((tensor_functor S R).op ⋙ algSpec (.of R)).map f.op).left
      (((tensor_functor S R).op ⋙ algSpec (.of R)).map g.op).left :=
    hR.of_iso' ((Over.forget _).mapIso (E.app (op M₃)))
      ((Over.forget _).mapIso (E.app (op M₁)))
      ((Over.forget _).mapIso (E.app (op M₂)))
      ((Over.forget _).mapIso (E.app (op M₀)))
      (congrArg (fun a => a.left) (E.hom.naturality p.op)).symm
      (congrArg (fun a => a.left) (E.hom.naturality q.op)).symm
      (congrArg (fun a => a.left) (E.hom.naturality f.op)).symm
      (congrArg (fun a => a.left) (E.hom.naturality g.op)).symm
  exact (isPushout_iff_spec_pullback _ _ _ _).mpr hnew

private theorem whisker_equifibered {J D E : Type*}
    [Category J] [Category D] [Category E] {A B : J ⥤ D}
    (α : A ⟶ B) (F G : D ⥤ E) (e : F ≅ G)
    (h : (Functor.whiskerRight α G).Equifibered) :
    (Functor.whiskerRight α F).Equifibered := by
  let hnat : Functor.whiskerRight α F ≫ (Functor.isoWhiskerLeft B e).hom =
      (Functor.isoWhiskerLeft A e).hom ≫ Functor.whiskerRight α G :=
    NatTrans.ext (funext fun i => e.hom.naturality (α.app i))
  let hArrow := Arrow.isoMk
    (f := Arrow.mk (Functor.whiskerRight α F))
    (g := Arrow.mk (Functor.whiskerRight α G))
    (Functor.isoWhiskerLeft A e) (Functor.isoWhiskerLeft B e)
    hnat.symm
  exact (MorphismProperty.arrow_mk_iso_iff
    (NatTrans.Equifibered (J := J) (C := E)) hArrow).mpr h

private theorem tensor_equifibered {J : Type v} [Category.{w} J]
    {A B : J ⥤ CommAlgCat.{u} S} (β : A ⟶ B)
    (h : (Functor.whiskerRight (NatTrans.op β)
      (algSpec (.of S) ⋙ scalar_functor
        (Spec.map (CommRingCat.ofHom (algebraMap S R))) ⋙ Over.forget _)).Equifibered) :
    (Functor.whiskerRight (NatTrans.op (Functor.whiskerRight β (tensor_functor S R)))
      (algSpec (.of R) ⋙ Over.forget _)).Equifibered :=
  whisker_equifibered (NatTrans.op β) _ _
    (Functor.isoWhiskerRight (tensor_spec_iso S R) (Over.forget _)) h

private theorem coefficient_triangle {K : Type u} [CommRing K]
    [Algebra S K] [Algebra R K] [IsScalarTower S R K] :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S R)) =
      Spec.map (CommRingCat.ofHom (algebraMap S K)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq S R K).symm

private theorem scalar_flag {K : Type u} [CommRing K]
    [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    (P : Over (Spec (.of S))) (Y : Over (Spec (.of K))) (q : Y.left ⟶ P.left)
    (h : IsPullback q Y.hom P.hom (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    let κ := Spec.map (CommRingCat.ofHom (algebraMap S R))
    let ρ := Spec.map (CommRingCat.ofHom (algebraMap R K))
    ∃ qR : Y.left ⟶ ((scalar_functor κ).obj P).left,
      IsPullback qR Y.hom ((scalar_functor κ).obj P).hom ρ ∧
      qR ≫ pullback.fst κ P.hom = Y.hom ≫ ρ ∧
      qR ≫ pullback.snd κ P.hom = q := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hw : (Y.hom ≫ ρ) ≫ κ = q ≫ P.hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun a => Y.hom ≫ a) (coefficient_triangle S R)).trans h.w.symm)
  let qR := pullback.lift (Y.hom ≫ ρ) q hw
  have hfst : qR ≫ pullback.fst κ P.hom = Y.hom ≫ ρ := pullback.lift_fst _ _ _
  have hsnd : qR ≫ pullback.snd κ P.hom = q := pullback.lift_snd _ _ _
  exact ⟨qR, inner_square h (IsPullback.of_hasPullback κ P.hom).flip
    hfst hsnd (coefficient_triangle S R), hfst, hsnd⟩

private theorem scalar_tower {B T U : Scheme.{u}} (κ : T ⟶ B) (ρ : U ⟶ T)
    (P : Over B) :
    ∃ E : (scalar_functor ρ).obj ((scalar_functor κ).obj P) ≅
      (scalar_functor (ρ ≫ κ)).obj P,
      E.hom.left ≫ pullback.fst (ρ ≫ κ) P.hom =
        pullback.fst ρ (pullback.fst κ P.hom) ∧
      E.hom.left ≫ pullback.snd (ρ ≫ κ) P.hom =
        pullback.snd ρ (pullback.fst κ P.hom) ≫ pullback.snd κ P.hom := by
  let E : (scalar_functor ρ).obj ((scalar_functor κ).obj P) ≅
      (scalar_functor (ρ ≫ κ)).obj P :=
    Over.isoMk (pullbackRightPullbackFstIso κ P.hom ρ)
      (pullbackRightPullbackFstIso_hom_fst κ P.hom ρ)
  exact ⟨E, pullbackRightPullbackFstIso_hom_fst κ P.hom ρ,
    pullbackRightPullbackFstIso_hom_snd κ P.hom ρ⟩

private theorem scalar_tower_eq {B T U : Scheme.{u}}
    (κ : T ⟶ B) (ρ : U ⟶ T) (ζ : U ⟶ B) (h : ρ ≫ κ = ζ) (P : Over B) :
    ∃ E : (scalar_functor ρ).obj ((scalar_functor κ).obj P) ≅
      (scalar_functor ζ).obj P,
      E.hom.left ≫ pullback.fst ζ P.hom =
        pullback.fst ρ (pullback.fst κ P.hom) ∧
      E.hom.left ≫ pullback.snd ζ P.hom =
        pullback.snd ρ (pullback.fst κ P.hom) ≫ pullback.snd κ P.hom := by
  subst ζ
  exact scalar_tower κ ρ P


end SchubertGeometry
