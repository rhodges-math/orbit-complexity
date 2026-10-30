import OrbitComplexity.FrobeniusSplitting.Normality.Models.ClosedChartQuotients
import OrbitComplexity.FrobeniusSplitting.Normality.NaturalModels
import OrbitComplexity.SchubertGeometry.FlagVariety.Properties
import OrbitComplexity.SchubertGeometry.Cells.Richardson
import Mathlib.CategoryTheory.Sigma.Basic

/-! # One coefficient model for specified closed flag supports -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace SchubertGeometry

universe u

private theorem coordinates_fp {X : Scheme.{u}} {J K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (U : J → X.Opens) (hU : ∀ j, IsAffineOpen (U j))
    (s : {s : Finset J // s.Nonempty}) :
    Algebra.FinitePresentation K ((FrobeniusSplitting.intersectionCoordinates f
      (FrobeniusSplitting.intersectionOpens U)).obj s) := by
  let D := FrobeniusSplitting.intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f
  have : IsAffine (D.obj (op s)).left :=
    FrobeniusSplitting.intersectionOpens_affine U hU (op s)
  have : LocallyOfFinitePresentation (D.obj (op s)).hom := by
    change LocallyOfFinitePresentation
      (((FrobeniusSplitting.intersectionOpens U).obj (op s)).ι ≫ f)
    infer_instance
  change RingHom.FinitePresentation
    (((D.obj (op s)).hom.appTop).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
  exact (D.obj (op s)).hom.finitePresentation_appTop.comp
    (RingHom.FinitePresentation.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv))

private theorem coordinates_smooth {X : Scheme.{u}} {J K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of K)) [Smooth f]
    (U : J → X.Opens) (hU : ∀ j, IsAffineOpen (U j))
    (s : {s : Finset J // s.Nonempty}) :
    Algebra.Smooth K ((FrobeniusSplitting.intersectionCoordinates f
      (FrobeniusSplitting.intersectionOpens U)).obj s) := by
  let D := FrobeniusSplitting.intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f
  have : IsAffine (D.obj (op s)).left :=
    FrobeniusSplitting.intersectionOpens_affine U hU (op s)
  have : Smooth (D.obj (op s)).hom := by
    change Smooth (((FrobeniusSplitting.intersectionOpens U).obj (op s)).ι ≫ f)
    infer_instance
  change (((D.obj (op s)).hom.appTop).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).Smooth
  exact (RingHom.Smooth.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv)).comp
      (HasRingHomProperty.appTop (P := @Smooth) (D.obj (op s)).hom inferInstance)

private theorem coordinates_open {X : Scheme.{u}} {J K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (f : X ⟶ Spec (.of K)) (U : J → X.Opens) (hU : ∀ j, IsAffineOpen (U j))
    {s t : {s : Finset J // s.Nonempty}} (a : s ⟶ t) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      ((FrobeniusSplitting.intersectionCoordinates f (FrobeniusSplitting.intersectionOpens U)).map
        a).hom.toRingHom)) := by
  let D := FrobeniusSplitting.intersectionOpens U ⋙ X.restrictFunctor ⋙ Over.map f
  have (r : {s : Finset J // s.Nonempty}ᵒᵖ) : IsAffine (D.obj r).left :=
    FrobeniusSplitting.intersectionOpens_affine U hU r
  have hopen : ∀ s t (b : s ⟶ t), IsOpenImmersion (D.map b).left := by
    intro s t b
    change IsOpenImmersion (X.homOfLE
      (leOfHom ((FrobeniusSplitting.intersectionOpens U).map b)))
    infer_instance
  exact FrobeniusSplitting.coordinateMaps_open (.of K) D hopen a.op

private theorem sigma_hom_finite {I C : Type u} [Category.{u} C]
    [∀ x y : C, Finite (x ⟶ y)] (x y : Σ _ : I, C) : Finite (x ⟶ y) := by
  classical
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  by_cases h : i = j
  · subst j
    exact Finite.of_surjective
      (fun f : x ⟶ y => (Sigma.SigmaHom.mk f : (⟨i, x⟩ : Σ _ : I, C) ⟶ ⟨i, y⟩))
      (by rintro ⟨f⟩; exact ⟨f, rfl⟩)
  · have : IsEmpty ((⟨i, x⟩ : Σ _ : I, C) ⟶ ⟨j, y⟩) := ⟨by
      intro f
      have hf : Sigma.SigmaHom (⟨i, x⟩ : Σ _ : I, C) ⟨j, y⟩ := f
      exact h (match hf with | .mk _ => rfl)⟩
    infer_instance

/-- The specified finite closed flag supports and the ambient flag atlas admit
one coefficient diagram. Every target is its reduced closed subvariety,
with the original coordinate comparisons and quotient maps retained. -/
theorem exists_closed_flag_models
    {K T I : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Finite T] [Finite I]
    (G : ReductiveGroups.ReductiveGroupData K)
    (Z : I → TopologicalSpace.Closeds (flagVariety G).scheme)
    (U : T → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t)) :
    let C := {s : Finset T // s.Nonempty}
    let F := FrobeniusSplitting.intersectionCoordinates (flagVariety G).toSpec
      (FrobeniusSplitting.intersectionOpens U)
    let j := fun i => (flagVariety G).closedInclusion (Z i)
    let B := fun i => FrobeniusSplitting.intersectionCoordinates
      ((j i).left ≫ (flagVariety G).toSpec) (FrobeniusSplitting.intersectionOpens (fun t => (j
        i).left ⁻¹ᵁ U t))
    let A := (Sigma.desc B).sum' F
    let H : (Σ _ : I, C) ⥤ C :=
      Sigma.desc (fun _ => FrobeniusSplitting.intersectionIndexMap (id : T → T))
    ∃ (S : Subalgebra ℤ K) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
      (e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K] A.obj x)
      (β : H ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ N) ⟶
        Sum.inl_ (Σ _ : I, C) C ⋙ N),
      S.FG ∧ (∀ x, Algebra.FinitePresentation S (N.obj x)) ∧
      (∀ x : C, Algebra.Smooth S (N.obj (.inr x))) ∧
      (∀ x y (a : x ⟶ y), (e y).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map a).hom) =
          (A.map a).hom.comp (e x).toAlgHom) ∧
      (∀ x, Function.Injective (fun z : N.obj x => e x ((1 : K) ⊗ₜ[S] z))) ∧
      (∀ x : Σ _ : I, C, (e (.inl x)).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (β.app x).hom) =
          (((FrobeniusSplitting.intersectionCoordinateMap (j x.1).left
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
          (CommRingCat.ofHom (N.map q).hom.toRingHom) := by
  classical
  let C := {s : Finset T // s.Nonempty}
  let F := FrobeniusSplitting.intersectionCoordinates (flagVariety G).toSpec
    (FrobeniusSplitting.intersectionOpens U)
  let X i := (flagVariety G).closedSubvariety (Z i)
  let j i := (flagVariety G).closedInclusion (Z i)
  let V i := fun t => (j i).left ⁻¹ᵁ U t
  let b i := (j i).left ≫ (flagVariety G).toSpec
  let B i := FrobeniusSplitting.intersectionCoordinates (b i) (FrobeniusSplitting.intersectionOpens
    (V i))
  let H : (Σ _ : I, C) ⥤ C :=
    Sigma.desc (fun _ => FrobeniusSplitting.intersectionIndexMap (id : T → T))
  have : IsSeparated (terminal.from (flagVariety G).scheme) := by
    rw [← terminal.comp_from (flagVariety G).toSpec]
    infer_instance
  have (i : I) : IsSeparated (terminal.from (X i).scheme) := by
    rw [← terminal.comp_from (X i).toSpec]
    infer_instance
  have : IsAffineHom (pullback.diagonal (terminal.from (flagVariety G).scheme)) :=
    inferInstance
  have : IsAffineHom (pullback.diagonal (terminal.from (flagVariety G).toOver.left)) := by
    change IsAffineHom (pullback.diagonal (terminal.from (flagVariety G).scheme))
    infer_instance
  have (i : I) : IsAffineHom (pullback.diagonal (terminal.from (X i).toOver.left)) := by
    change IsAffineHom (pullback.diagonal (terminal.from (X i).scheme))
    infer_instance
  have hV (i : I) (t : T) : IsAffineOpen (V i t) := (hU t).preimage (j i).left
  have (i : I) : LocallyOfFinitePresentation (b i) := by
    rw [show b i = (X i).toSpec from (j i).w]
    infer_instance
  have (s : C) : Algebra.FinitePresentation K (F.obj s) :=
    coordinates_fp (flagVariety G).toSpec U hU s
  have (x : Σ _ : I, C) : Algebra.FinitePresentation K ((Sigma.desc B).obj x) :=
    coordinates_fp (b x.1) (V x.1) (hV x.1) x.2
  have (s : C) : Algebra.Smooth K (F.obj s) :=
    coordinates_smooth (flagVariety G).toSpec U hU s
  have (x y : Σ _ : I, C) : Finite (x ⟶ y) := sigma_hom_finite x y
  let δ i := FrobeniusSplitting.intersectionCoordinateMap
    (j i).left (flagVariety G).toSpec (V i) U id (fun _ => le_rfl)
  let α : H ⋙ F ⟶ Sigma.desc B :=
    { app := fun x => (δ x.1).app x.2
      naturality := by rintro ⟨i, s⟩ ⟨_, t⟩ ⟨a⟩; exact (δ i).naturality a }
  have hopenB : ∀ x y (a : x ⟶ y), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((Sigma.desc B).map a).hom.toRingHom)) := by
    rintro ⟨i, s⟩ ⟨_, t⟩ ⟨a⟩
    exact coordinates_open (b i) (V i) (hV i) a
  let smoothNodes : Set ((Σ _ : I, C) ⊕ C) := Set.range Sum.inr
  have hsm : ∀ x ∈ smoothNodes, Algebra.Smooth K (((Sigma.desc B).sum' F).obj x) := by
    rintro (x | x) ⟨y, hy⟩
    · cases hy
    · exact inferInstanceAs (Algebra.Smooth K (F.obj x))
  obtain ⟨S, N, e, β, hS, hfp, hsmS, hn, hinj, hβ, hopen, hpush⟩ :=
    FrobeniusSplitting.exists_natural_open_models (Sigma.desc B) F hopenB
      (fun _ _ a => coordinates_open (flagVariety G).toSpec U hU a) H α smoothNodes hsm
  refine ⟨S, N, e, β, hS, hfp, fun x => hsmS (.inr x) ⟨x, rfl⟩, hn, hinj, hβ, ?_,
    hopen, hpush⟩
  intro x z
  have hs : Function.Surjective (α.app x).hom :=
    FrobeniusSplitting.closed_intersection_quotients
      (j x.1).left (flagVariety G).toSpec U hU x.2
  obtain ⟨a, ha⟩ := hs (e (.inl x) z)
  let w := (e (.inr (H.obj x))).symm a
  refine ⟨w, (e (.inl x)).injective ?_⟩
  have hleft := AlgHom.congr_fun (hβ x) w
  have hright : (α.app x).hom (e (.inr (H.obj x)) w) = e (.inl x) z := by
    exact (e (.inr (H.obj x))).apply_symm_apply a ▸ ha
  exact Eq.trans hleft hright


end SchubertGeometry
