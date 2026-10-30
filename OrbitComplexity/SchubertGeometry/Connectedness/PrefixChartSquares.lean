import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixSquareComparisons
import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.Sums.Basic

set_option autoImplicit false

/-! # Mixed squares of the specified closed-target atlas

The finite family contains each restriction arrow in each closed target.
Its scalar comparisons come from the prescribed coordinate equivalences
and quotient-map equations. All mixed squares are retained at one stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u v

private theorem affine_fp {R : Type u} [CommRing R] (M : CommAlgCat.{u} R)
    (h : Algebra.FinitePresentation R M) :
    LocallyOfFinitePresentation ((algSpec (.of R)).obj (op M)).hom := by
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R M)))
  apply (LocallyOfFinitePresentation.SpecMap_iff
    (CommRingCat.ofHom (algebraMap R M))).mpr
  change (algebraMap R M).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  exact h

private theorem functor_op_square {C D : Type*} [Category C] [Category D]
    (F : Cᵒᵖ ⥤ D) {M₀ M₁ M₂ M₃ : C}
    (f : M₀ ⟶ M₁) (g : M₀ ⟶ M₂) (p : M₁ ⟶ M₃) (q : M₂ ⟶ M₃)
    (h : f ≫ p = g ≫ q) :
    F.map p.op ≫ F.map f.op = F.map q.op ≫ F.map g.op := by
  have hh : p.op ≫ f.op = q.op ≫ g.op :=
    congrArg (fun k : M₀ ⟶ M₃ => k.op) h
  rw [← F.map_comp, ← F.map_comp, hh]

private theorem spec_square_comm {R : Type u} [CommRing R]
    {M₀ M₁ M₂ M₃ : CommAlgCat.{u} R}
    (f : M₀ ⟶ M₁) (g : M₀ ⟶ M₂) (p : M₁ ⟶ M₃) (q : M₂ ⟶ M₃)
    (h : f ≫ p = g ≫ q) :
    (algSpec (.of R)).map p.op ≫ (algSpec (.of R)).map f.op =
      (algSpec (.of R)).map q.op ≫ (algSpec (.of R)).map g.op :=
  functor_op_square (algSpec (.of R)) f g p q h

private def square_result {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} (M₀ M₁ M₂ M₃ : J → CommAlgCat.{u} S)
    (f : ∀ j, M₀ j ⟶ M₁ j) (g : ∀ j, M₀ j ⟶ M₂ j)
    (p : ∀ j, M₁ j ⟶ M₃ j) (q : ∀ j, M₂ j ⟶ M₃ j)
    (start : CoefficientStage S) : Prop :=
  ∃ (k : CoefficientStage S) (_ : start ≤ k), ∀ j,
    let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
    IsPullback (chosenScalarArrow κ ((algSpec (.of S)).map (p j).op)).left
      (chosenScalarArrow κ ((algSpec (.of S)).map (q j).op)).left
      (chosenScalarArrow κ ((algSpec (.of S)).map (f j).op)).left
      (chosenScalarArrow κ ((algSpec (.of S)).map (g j).op)).left

private theorem retain_square_family
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type v} [Fintype J] (M₀ M₁ M₂ M₃ : J → CommAlgCat.{u} S)
    (A₀ A₁ A₂ A₃ : J → CommAlgCat.{u} K)
    (e₀ : ∀ j, K ⊗[S] M₀ j ≃ₐ[K] A₀ j) (e₁ : ∀ j, K ⊗[S] M₁ j ≃ₐ[K] A₁ j)
    (e₂ : ∀ j, K ⊗[S] M₂ j ≃ₐ[K] A₂ j) (e₃ : ∀ j, K ⊗[S] M₃ j ≃ₐ[K] A₃ j)
    (h₀ : ∀ j, Algebra.FinitePresentation S (M₀ j))
    (h₁ : ∀ j, Algebra.FinitePresentation S (M₁ j))
    (h₂ : ∀ j, Algebra.FinitePresentation S (M₂ j))
    (h₃ : ∀ j, Algebra.FinitePresentation S (M₃ j))
    (f₀ : ∀ j, M₀ j ⟶ M₁ j) (g₀ : ∀ j, M₀ j ⟶ M₂ j)
    (p₀ : ∀ j, M₁ j ⟶ M₃ j) (q₀ : ∀ j, M₂ j ⟶ M₃ j)
    (f : ∀ j, A₀ j ⟶ A₁ j) (g : ∀ j, A₀ j ⟶ A₂ j)
    (p : ∀ j, A₁ j ⟶ A₃ j) (q : ∀ j, A₂ j ⟶ A₃ j)
    (hw : ∀ j, f₀ j ≫ p₀ j = g₀ j ≫ q₀ j)
    (hf : ∀ j, (e₁ j).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (f₀ j).hom) =
      (f j).hom.comp (e₀ j).toAlgHom)
    (hg : ∀ j, (e₂ j).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (g₀ j).hom) =
      (g j).hom.comp (e₀ j).toAlgHom)
    (hp : ∀ j, (e₃ j).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (p₀ j).hom) =
      (p j).hom.comp (e₁ j).toAlgHom)
    (hq : ∀ j, (e₃ j).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (q₀ j).hom) =
      (q j).hom.comp (e₂ j).toAlgHom)
    (hcart : ∀ j, IsPullback ((algSpec (.of K)).map (p j).op).left
      ((algSpec (.of K)).map (q j).op).left
      ((algSpec (.of K)).map (f j).op).left
      ((algSpec (.of K)).map (g j).op).left)
    (start : CoefficientStage S) : square_result S M₀ M₁ M₂ M₃ f₀ g₀ p₀ q₀ start := by
  let (j : J) : LocallyOfFinitePresentation ((algSpec (.of S)).obj (op (M₀ j))).hom :=
    affine_fp (M₀ j) (h₀ j)
  let (j : J) : LocallyOfFinitePresentation ((algSpec (.of S)).obj (op (M₁ j))).hom :=
    affine_fp (M₁ j) (h₁ j)
  let (j : J) : LocallyOfFinitePresentation ((algSpec (.of S)).obj (op (M₂ j))).hom :=
    affine_fp (M₂ j) (h₂ j)
  let (j : J) : LocallyOfFinitePresentation ((algSpec (.of S)).obj (op (M₃ j))).hom :=
    affine_fp (M₃ j) (h₃ j)
  let (j : J) : IsAffine ((algSpec (.of S)).obj (op (M₀ j))).left := by
    change IsAffine (Spec (.of (M₀ j)))
    infer_instance
  let (j : J) : IsAffine ((algSpec (.of S)).obj (op (M₁ j))).left := by
    change IsAffine (Spec (.of (M₁ j)))
    infer_instance
  let (j : J) : IsAffine ((algSpec (.of S)).obj (op (M₂ j))).left := by
    change IsAffine (Spec (.of (M₂ j)))
    infer_instance
  let (j : J) : IsAffine ((algSpec (.of S)).obj (op (M₃ j))).left := by
    change IsAffine (Spec (.of (M₃ j)))
    infer_instance
  exact exists_prefix_square_stage S hS
    (fun j => (algSpec (.of S)).obj (op (M₃ j)))
    (fun j => (algSpec (.of S)).obj (op (M₁ j)))
    (fun j => (algSpec (.of S)).obj (op (M₂ j)))
    (fun j => (algSpec (.of S)).obj (op (M₀ j)))
    (fun j => (algSpec (.of S)).map (p₀ j).op)
    (fun j => (algSpec (.of S)).map (q₀ j).op)
    (fun j => (algSpec (.of S)).map (f₀ j).op)
    (fun j => (algSpec (.of S)).map (g₀ j).op)
    (fun j => spec_square_comm (f₀ j) (g₀ j) (p₀ j) (q₀ j) (hw j))
    (fun j => prefix_model_cartesian _ _ _ _ _ _ _ _
      (e₀ j) (e₁ j) (e₂ j) (e₃ j) (f₀ j) (g₀ j) (p₀ j) (q₀ j)
      (f j) (g j) (p j) (q j) (hf j) (hg j) (hp j) (hq j) (hcart j)) start

private theorem split_square_result {J C L : Type*} [Category C]
    (P : L → (i : J) → (s t : C) → (s ⟶ t) → Prop) (Q : L → Prop)
    (h : ∃ k, ∃ (_ : Q k), ∀ r : J × (Σ s : C, Σ t : C, s ⟶ t),
      P k r.1 r.2.1 r.2.2.1 r.2.2.2) :
    ∃ k, ∃ (_ : Q k), ∀ i s t a, P k i s t a := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, hk, fun i s t a => h (i, ⟨s, t, a⟩)⟩

/-- All mixed quotient squares of a specified finite closed-target coordinate
model become Cartesian at one stage. The coordinate diagram, quotient maps
and tensor comparisons are the specified ones. -/
theorem exists_prefix_chart_squares
    {K T I : Type u} [CommRing K] [Finite T] [Finite I]
    {Y : Scheme.{u}} (X : I → Scheme.{u})
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    [∀ i, IsAffineHom (pullback.diagonal (terminal.from (X i)))]
    (j : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (j i)]
    (base : Y ⟶ Spec (.of K)) (U : T → Y.Opens) (hU : ∀ t, IsAffineOpen (U t)) :
    let C := {s : Finset T // s.Nonempty}
    let F := intersectionCoordinates base (intersectionOpens U)
    let B := fun i => intersectionCoordinates (j i ≫ base) (intersectionOpens (fun t => j i ⁻¹ᵁ U
      t))
    let A := (Sigma.desc B).sum' F
    let H : (Σ _ : I, C) ⥤ C := Sigma.desc (fun _ => intersectionIndexMap (id : T → T))
    ∀ (S : Subalgebra ℤ K) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
      (e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K] A.obj x)
      (β : H ⋙ (Sum.inr_ _ _ ⋙ N) ⟶ Sum.inl_ _ _ ⋙ N),
      S.FG →
      (∀ x, Algebra.FinitePresentation S (N.obj x)) →
      (∀ x y (a : x ⟶ y), (e y).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map a).hom) =
        (A.map a).hom.comp (e x).toAlgHom) →
      (∀ x : Σ _ : I, C, (e (.inl x)).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (β.app x).hom) =
        ((intersectionCoordinateMap (j x.1) base (fun t => j x.1 ⁻¹ᵁ U t) U id
          (fun _ => le_rfl)).app x.2).hom.comp (e (.inr (H.obj x))).toAlgHom) →
      ∀ start : CoefficientStage S,
      ∃ (k : CoefficientStage S) (_ : start ≤ k), ∀ i (s t : Cᵒᵖ) (a : s ⟶ t),
        let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
        let b := (Sum.inl_ (Σ _ : I, C) C).map
          (show (⟨i, t.unop⟩ : Σ _ : I, C) ⟶ ⟨i, s.unop⟩ from Sigma.SigmaHom.mk a.unop)
        let f := (Sum.inr_ (Σ _ : I, C) C).map
          ((intersectionIndexMap (id : T → T)).map a.unop)
        IsPullback
          (chosenScalarArrow κ ((algSpec (.of S)).map (N.map b).op)).left
          (chosenScalarArrow κ ((algSpec (.of S)).map (β.app ⟨i, s.unop⟩).op)).left
          (chosenScalarArrow κ ((algSpec (.of S)).map (β.app ⟨i, t.unop⟩).op)).left
          (chosenScalarArrow κ ((algSpec (.of S)).map (N.map f).op)).left := by
  classical
  dsimp only
  intro S N e β hS hfp hn hβ start
  let C := {s : Finset T // s.Nonempty}
  let H₀ := intersectionIndexMap (id : T → T)
  let F := intersectionCoordinates base (intersectionOpens U)
  let B := fun i => intersectionCoordinates (j i ≫ base) (intersectionOpens (fun t => j i ⁻¹ᵁ U t))
  let E := I × (Σ s : Cᵒᵖ, Σ t : Cᵒᵖ, s ⟶ t)
  let : Fintype E := Fintype.ofFinite E
  let source (r : E) : Σ _ : I, C := ⟨r.1, r.2.2.1.unop⟩
  let target (r : E) : Σ _ : I, C := ⟨r.1, r.2.1.unop⟩
  let edge (r : E) : source r ⟶ target r := Sigma.SigmaHom.mk r.2.2.2.unop
  let amb (r : E) := (Sum.inr_ (Σ _ : I, C) C).map (H₀.map r.2.2.2.unop)
  let sub (r : E) := (Sum.inl_ (Σ _ : I, C) C).map (edge r)
  let M₀ (r : E) := N.obj (.inr (H₀.obj r.2.2.1.unop))
  let M₁ (r : E) := N.obj (.inl (source r))
  let M₂ (r : E) := N.obj (.inr (H₀.obj r.2.1.unop))
  let M₃ (r : E) := N.obj (.inl (target r))
  let A₀ (r : E) := F.obj (H₀.obj r.2.2.1.unop)
  let A₁ (r : E) := (B r.1).obj r.2.2.1.unop
  let A₂ (r : E) := F.obj (H₀.obj r.2.1.unop)
  let A₃ (r : E) := (B r.1).obj r.2.1.unop
  let δ (i : I) := intersectionCoordinateMap (j i) base (fun t => j i ⁻¹ᵁ U t) U id
    (fun _ => le_rfl)
  apply split_square_result
  exact retain_square_family S hS M₀ M₁ M₂ M₃ A₀ A₁ A₂ A₃
    (fun r => e (.inr (H₀.obj r.2.2.1.unop))) (fun r => e (.inl (source r)))
    (fun r => e (.inr (H₀.obj r.2.1.unop))) (fun r => e (.inl (target r)))
    (fun r => hfp (.inr (H₀.obj r.2.2.1.unop))) (fun r => hfp (.inl (source r)))
    (fun r => hfp (.inr (H₀.obj r.2.1.unop))) (fun r => hfp (.inl (target r)))
    (fun r => β.app (source r)) (fun r => N.map (amb r))
    (fun r => N.map (sub r)) (fun r => β.app (target r))
    (fun r => (δ r.1).app r.2.2.1.unop) (fun r => F.map (H₀.map r.2.2.2.unop))
    (fun r => (B r.1).map r.2.2.2.unop) (fun r => (δ r.1).app r.2.1.unop)
    (fun r => (β.naturality (edge r)).symm)
    (fun r => hβ (source r)) (fun r => hn _ _ (amb r))
    (fun r => hn _ _ (sub r)) (fun r => hβ (target r))
    (fun r => prefix_coordinates_cartesian (j r.1) base U id hU
      (fun t => (hU t).preimage (j r.1)) r.2.1 r.2.2.1 r.2.2.2) start

end SchubertGeometry
