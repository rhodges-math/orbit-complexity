import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Normality.Models.ClosedFlagModels
import OrbitComplexity.FrobeniusSplitting.Normality.Models.FiniteRelations
import OrbitComplexity.FrobeniusSplitting.Normality.Models.ClosedQuotientAtlas
import Mathlib.RingTheory.Extension.Generators
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

set_option autoImplicit false

/-! # Closed Schubert targets over a common coefficient ring

Finite generator lifts retain the quotient maps in a finite closed-target
atlas. The quotient equations are retained before any gluing is performed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting Opposite
open scoped TensorProduct

namespace SchubertGeometry

universe u v

private def tensor_right_map {S : Type*} [CommRing S]
    (R : Type*) [CommRing R] [Algebra S R]
    {A B : Type*} [CommRing A] [CommRing B] [Algebra S A] [Algebra S B]
    (f : A →ₐ[S] B) : R ⊗[S] A →ₐ[R] R ⊗[S] B :=
  Algebra.TensorProduct.map (AlgHom.id R R) f

private theorem surjective_of_generator_lifts
    {S A B I : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] (P : Algebra.Generators S B I)
    (f : A →ₐ[S] B) (w : I → A) (hw : ∀ i, f (w i) = P.val i) :
    Function.Surjective f := by
  have he : f.comp (MvPolynomial.aeval w) = MvPolynomial.aeval P.val := by
    ext i
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hw i
  intro b
  obtain ⟨p, hp⟩ := P.aeval_val_surjective b
  refine ⟨MvPolynomial.aeval w p, ?_⟩
  exact (congrArg (fun g : MvPolynomial I S →ₐ[S] B => g p) he).trans hp

private theorem tensor_cokernel_exact
    {S A B : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] (R : Type*) [CommRing R] [Algebra S R]
    (f : A →ₐ[S] B) :
    Function.Exact (f.toLinearMap.lTensor R)
      (f.toLinearMap.range.mkQ.lTensor R) :=
  lTensor_exact R (LinearMap.exact_iff.mpr
    (Submodule.ker_mkQ (p := f.toLinearMap.range)))
    (Submodule.mkQ_surjective _)

private theorem tensor_cokernel_zero
    {S A B : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] (K : Type*) [CommRing K] [Algebra S K]
    (f : A →ₐ[S] B) (hf : Function.Surjective (tensor_right_map K f)) (b : B) :
    (1 : K) ⊗ₜ[S] f.toLinearMap.range.mkQ b = 0 := by
  have h := (tensor_cokernel_exact K f ((1 : K) ⊗ₜ[S] b)).mpr
    (hf ((1 : K) ⊗ₜ[S] b))
  exact h

private theorem surjective_of_cokernel_zero
    {S A B I : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] (R : Type*) [CommRing R] [Algebra S R]
    (P : Algebra.Generators S B I) (f : A →ₐ[S] B)
    (hz : ∀ i, (1 : R) ⊗ₜ[S] f.toLinearMap.range.mkQ (P.val i) = 0) :
    Function.Surjective (tensor_right_map R f) := by
  classical
  have hlift (i : I) : ∃ w : R ⊗[S] A,
      tensor_right_map R f w = (1 : R) ⊗ₜ[S] P.val i :=
    (tensor_cokernel_exact R f ((1 : R) ⊗ₜ[S] P.val i)).mp (hz i)
  choose w hw using hlift
  exact surjective_of_generator_lifts (P.baseChange R) (tensor_right_map R f) w hw

private theorem retain_surjective_family
    {K : Type u} [Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {I : Type v} [Finite I] (A B : I → Type u)
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra S (A i)] [∀ i, Algebra S (B i)]
    [∀ i, Algebra.FiniteType S (B i)]
    (f : ∀ i, A i →ₐ[S] B i)
    (hf : ∀ i, Function.Surjective (tensor_right_map K (f i))) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let _ : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let _ : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      R.FG ∧ ∀ i, Function.Surjective (tensor_right_map R (f i)) := by
  classical
  choose n hP using fun i =>
    (Algebra.FiniteType.iff_exists_generators (R := S) (S := B i)).mp inferInstance
  let P (i : I) : Algebra.Generators S (B i) (Fin (n i)) := Classical.choice (hP i)
  let J := Σ i : I, Fin (n i)
  let Q (j : J) := B j.1 ⧸ (f j.1).toLinearMap.range
  let x (j : J) : Q j := (f j.1).toLinearMap.range.mkQ ((P j.1).val j.2)
  have hx (j : J) : (1 : K) ⊗ₜ[S] x j = 0 :=
    tensor_cokernel_zero K (f j.1) (hf j.1) ((P j.1).val j.2)
  obtain ⟨R, hSR, hR, hzero⟩ := exists_retained_zero_relations S hS Q x hx
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  exact ⟨R, hSR, hR, fun i =>
    surjective_of_cokernel_zero R (P i) (f i) (fun k => hzero ⟨i, k⟩)⟩

private theorem enrich_four {A : Sort*} {B : A → Sort*} {C : ∀ a, B a → Sort*}
    {D : ∀ a b, C a b → Sort*} {P Q : ∀ a b c, D a b c → Prop}
    (h : ∃ a b c d, P a b c d)
    (next : ∀ a b c d, P a b c d → Q a b c d) :
    ∃ a b c d, P a b c d ∧ Q a b c d := by
  obtain ⟨a, b, c, d, hp⟩ := h
  exact ⟨a, b, c, d, hp, next a b c d hp⟩

/-- A finite family of Schubert supports has a common coordinate model whose
chart quotient maps are surjective after a finite coefficient extension.
Every original coordinate comparison and open-chart condition is retained. -/
theorem exists_prefix_chart_quotients
    {K T I : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Finite T] [Finite I]
    (G : ReductiveGroupData K) (w : I → G.weylGroup)
    (U : T → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t)) :
    let C := {s : Finset T // s.Nonempty}
    let F := intersectionCoordinates (flagVariety G).toSpec (intersectionOpens U)
    let j := fun i => (flagVariety G).closedInclusion (schubertSupport G (w i))
    let B := fun i => intersectionCoordinates
      ((j i).left ≫ (flagVariety G).toSpec) (intersectionOpens (fun t => (j i).left ⁻¹ᵁ U t))
    let A := (Sigma.desc B).sum' F
    let H : (Σ _ : I, C) ⥤ C :=
      Sigma.desc (fun _ => intersectionIndexMap (id : T → T))
    ∃ (S : Subalgebra ℤ K) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
      (e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K] A.obj x)
      (β : H ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ N) ⟶ Sum.inl_ (Σ _ : I, C) C ⋙ N),
      (S.FG ∧ (∀ x, Algebra.FinitePresentation S (N.obj x)) ∧
        (∀ x : C, Algebra.Smooth S (N.obj (.inr x))) ∧
        (∀ x y (a : x ⟶ y), (e y).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (N.map a).hom) =
            (A.map a).hom.comp (e x).toAlgHom) ∧
        (∀ x, Function.Injective (fun z : N.obj x => e x ((1 : K) ⊗ₜ[S] z))) ∧
        (∀ x : Σ _ : I, C, (e (.inl x)).toAlgHom.comp
          (Algebra.TensorProduct.lTensor (S := K) K (β.app x).hom) =
            (((intersectionCoordinateMap (j x.1).left
              (flagVariety G).toSpec (fun t => (j x.1).left ⁻¹ᵁ U t)
              U id (fun _ => le_rfl)).app x.2).hom).comp
                (e (.inr (H.obj x))).toAlgHom) ∧
        (∀ x, Function.Surjective
          (Algebra.TensorProduct.lTensor (S := K) K (β.app x).hom)) ∧
        (∀ x y (a : x ⟶ y), IsOpenImmersion
          (Spec.map (CommRingCat.ofHom (N.map a).hom.toRingHom))) ∧
        ∀ (x y z t) (a : x ⟶ y) (b : x ⟶ z) (p : y ⟶ t) (q : z ⟶ t),
          IsPushout (CommRingCat.ofHom (A.map a).hom.toRingHom)
            (CommRingCat.ofHom (A.map b).hom.toRingHom)
            (CommRingCat.ofHom (A.map p).hom.toRingHom)
            (CommRingCat.ofHom (A.map q).hom.toRingHom) →
          IsPushout (CommRingCat.ofHom (N.map a).hom.toRingHom)
            (CommRingCat.ofHom (N.map b).hom.toRingHom)
            (CommRingCat.ofHom (N.map p).hom.toRingHom)
            (CommRingCat.ofHom (N.map q).hom.toRingHom)) ∧
      ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
        let _ : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
        let _ : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
        R.FG ∧ ∀ x : Σ _ : I, C,
          Function.Surjective
            (Algebra.TensorProduct.lTensor (S := R) R (β.app x).hom) := by
  exact enrich_four (exists_closed_flag_models G (fun i => schubertSupport G (w i)) U hU)
    (fun S N _e β h =>
      let _ : ∀ x, Algebra.FinitePresentation S (N.obj x) := h.2.1
      retain_surjective_family S h.1
        (fun x => N.obj (.inr ((Sigma.desc (fun _ : I =>
          intersectionIndexMap (id : T → T))).obj x)))
        (fun x => N.obj (.inl x)) (fun x => (β.app x).hom) h.2.2.2.2.2.2.1)

-- GAP: C6-STAGE. Retain the finite mixed quotient Cartesian squares with both
-- projections, glue these closed charts, and compare their ambient model to
-- the prescribed flag model before applying the endpoint word induction.

end SchubertGeometry
