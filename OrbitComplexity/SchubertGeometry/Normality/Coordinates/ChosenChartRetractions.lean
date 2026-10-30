import OrbitComplexity.SchubertGeometry.Normality.Coordinates.ChosenRichardsonKernels
import OrbitComplexity.FrobeniusSplitting.Normality.Retractions.RetractionEnlargement
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Retractions on a finite prescribed chart family

The finite source covers are chosen on the inverse images of the chosen
target charts. A single coefficient enlargement splits all their original
section maps.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u v

open private chosen_patch_retraction
  from OrbitComplexity.SchubertGeometry.Normality.Coordinates.ChosenRichardsonKernels

private theorem join_retractions {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type v} [Finite I]
    (M N : I → Type u) [∀ i, CommRing (M i)] [∀ i, CommRing (N i)]
    [∀ i, Algebra S (M i)] [∀ i, Algebra S (N i)]
    (g : ∀ i, M i →ₐ[S] N i)
    (h : ∀ i, ∃ T : Subalgebra ℤ K, T.FG ∧ ∃ hST : S ≤ T,
      let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      ∃ r : T ⊗[S] N i →ₗ[T] T ⊗[S] M i,
        r.comp (Algebra.TensorProduct.lTensor (S := T) T (g i)).toLinearMap =
          LinearMap.id) :
    ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ hSR : S ≤ R,
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      ∀ i, ∃ r : R ⊗[S] N i →ₗ[R] R ⊗[S] M i,
        r.comp (Algebra.TensorProduct.lTensor (S := R) R (g i)).toLinearMap =
          LinearMap.id := by
  classical
  let : Fintype I := Fintype.ofFinite I
  choose T hT hST hr using h
  have hfg (s : Finset I) : (s.sup T).FG := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sup_empty] using
        (Subalgebra.fg_bot : (⊥ : Subalgebra ℤ K).FG)
    | @insert i s hi ih =>
        simpa only [Finset.sup_insert] using (hT i).sup ih
  let R : Subalgebra ℤ K := S ⊔ Finset.univ.sup T
  have hR : R.FG := hS.sup (hfg Finset.univ)
  have hSR : S ≤ R := le_sup_left
  have hTR (i : I) : T i ≤ R :=
    (show T i ≤ Finset.univ.sup T from Finset.le_sup (Finset.mem_univ i)).trans
      le_sup_right
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  refine ⟨R, hR, hSR, ?_⟩
  dsimp only
  intro i
  let : Algebra S (T i) := (Subalgebra.inclusion (hST i)).toAlgebra
  let : Algebra (T i) R := (Subalgebra.inclusion (hTR i)).toAlgebra
  let : IsScalarTower S (T i) R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨r, hri⟩ := hr i
  exact retraction_enlarge (T := R) (g i) r hri

/-- A finite affine chart family of the specified target admits finite affine
source covers whose specified endpoint section maps all split after one
coefficient enlargement. -/
theorem exists_chosen_chart_retractions {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type v} [Finite I]
    {X₀ Y₀ X Y : Scheme.{u}}
    (x₀ : X₀ ⟶ Spec (.of S)) (y₀ : Y₀ ⟶ Spec (.of S))
    [LocallyOfFinitePresentation x₀] [LocallyOfFinitePresentation y₀]
    (x : X ⟶ Spec (.of K)) (y : Y ⟶ Spec (.of K))
    (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y)
    (hf₀ : f₀ ≫ y₀ = x₀) (hf : f ≫ y = x)
    [QuasiCompact f₀] [QuasiCompact f] [Surjective f] [IsReduced Y]
    (qX : X ⟶ X₀) (qY : Y ⟶ Y₀)
    (hX : IsPullback qX x x₀
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY y y₀
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hsquare : qX ≫ f₀ = f ≫ qY)
    (W : I → Y₀.Opens) (hW : ∀ i, IsAffineOpen (W i)) :
    let sourceBase (i) := (f₀ ⁻¹ᵁ W i).ι ≫ x₀
    let targetBase (i) := (W i).ι ≫ y₀
    let fR (i) : Over.mk (sourceBase i) ⟶ Over.mk (targetBase i) :=
      Over.homMk (f₀ ∣_ W i) (by
        change (f₀ ∣_ W i) ≫ ((W i).ι ≫ y₀) = (f₀ ⁻¹ᵁ W i).ι ≫ x₀
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hf₀])
    ∃ V : ∀ i, (f₀ ⁻¹ᵁ W i).toScheme.OpenCover.{u},
      (∀ i, Finite (V i).I₀) ∧ (∀ i j, IsAffine ((V i).X j)) ∧
      ∃ R : Subalgebra ℤ K, R.FG ∧ ∃ hSR : S ≤ R,
        let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
        ∀ i, ∃ r : R ⊗[S] (∀ j, ((algΓ (.of S)).obj
            (Over.mk ((V i).f j ≫ sourceBase i))).unop) →ₗ[R]
              R ⊗[S] ((algΓ (.of S)).obj (Over.mk (targetBase i))).unop,
          r.comp (Algebra.TensorProduct.lTensor (S := R) R
            (affineCoverSectionMap (fR i) (V i))).toLinearMap = LinearMap.id := by
  classical
  intro sourceBase targetBase fR
  choose V hVfin hVaff T hT hST hr using
    (fun i => chosen_patch_retraction S hS x₀ y₀ x y f₀ f hf₀ hf
      qX qY hX hY hsquare (W i) (hW i))
  let M (i) : Type u := ((algΓ (.of S)).obj (Over.mk (targetBase i))).unop
  let N (i) : Type u := ∀ j, ((algΓ (.of S)).obj
    (Over.mk ((V i).f j ≫ sourceBase i))).unop
  let g (i) : M i →ₐ[S] N i := affineCoverSectionMap (fR i) (V i)
  obtain ⟨R, hR, hSR, hret⟩ := join_retractions S hS M N g
    (fun i => ⟨T i, hT i, hST i, hr i⟩)
  exact ⟨V, hVfin, hVaff, R, hR, hSR, hret⟩

end SchubertGeometry
