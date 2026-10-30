import Batteries.Tactic.OpenPrivate
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing
import OrbitComplexity.SchubertGeometry.Normality.Models.ClosedFlagModels
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateCocones
import OrbitComplexity.FrobeniusSplitting.Normality.IntersectionSquares
import OrbitComplexity.FrobeniusSplitting.Normality.DirectedSpectra
import Mathlib.CategoryTheory.Sums.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

set_option autoImplicit false

/-! # Closed prefix targets from their coordinate diagram

The identity labeling of affine intersections retains the quotient
transformation. The canonical coordinate cocones determine the original
closed inclusions and place their coefficient models in the chosen flag
model at one common stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ReductiveGroups
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u v

open private target_result from OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing

private theorem index_identity (T : Type u) :
    intersectionIndexMap (id : T → T) = 𝟭 {s : Finset T // s.Nonempty} := by
  classical
  exact CategoryTheory.Functor.ext (fun s => Subtype.ext Finset.image_id)
    (fun _ _ _ => Subsingleton.elim _ _)

private def index_iso (T : Type u) :
    intersectionIndexMap (id : T → T) ≅ 𝟭 {s : Finset T // s.Nonempty} :=
  eqToIso (index_identity T)

private def quotient_component {C : Type u} [Category.{u} C] {I R : Type u}
    [CommRing R] (H : C ⥤ C) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} R)
    (β : (Sigma.desc (fun _ : I => H)) ⋙ (Sum.inr_ _ _ ⋙ N) ⟶ Sum.inl_ _ _ ⋙ N)
    (i : I) : H ⋙ (Sum.inr_ _ _ ⋙ N) ⟶
      Sigma.incl (C := fun _ : I => C) i ⋙ (Sum.inl_ _ _ ⋙ N) where
  app c := β.app ⟨i, c⟩
  naturality _ _ f := β.naturality (Sigma.SigmaHom.mk f)

private theorem reindex_directed {C : Type u} [Category.{u} C]
    {R : Type u} [CommRing R] (H : C ⥤ C) (hH : H = 𝟭 C)
    (D : C ⥤ CommAlgCat.{u} R)
    [((D.op ⋙ algSpec (.of R) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected] :
    (((H ⋙ D).op ⋙ algSpec (.of R) ⋙ Over.forget _) ⋙
      Scheme.forget).IsLocallyDirected := by
  subst H
  exact inferInstanceAs
    (((D.op ⋙ algSpec (.of R) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected)

private theorem retain_refinements {C : Type u} [Category.{u} C]
    {R K : Type u} [CommRing R] [CommRing K]
    (D : C ⥤ CommAlgCat.{u} R) (F : C ⥤ CommAlgCat.{u} K)
    (hretain : ∀ (i j k l : C) (f : i ⟶ j) (g : i ⟶ k) (p : j ⟶ l) (q : k ⟶ l),
      IsPushout (CommRingCat.ofHom (F.map f).hom.toRingHom)
        (CommRingCat.ofHom (F.map g).hom.toRingHom)
        (CommRingCat.ofHom (F.map p).hom.toRingHom)
        (CommRingCat.ofHom (F.map q).hom.toRingHom) →
      IsPushout (CommRingCat.ofHom (D.map f).hom.toRingHom)
        (CommRingCat.ofHom (D.map g).hom.toRingHom)
        (CommRingCat.ofHom (D.map p).hom.toRingHom)
        (CommRingCat.ofHom (D.map q).hom.toRingHom))
    (hrefine : ∀ (i j k : C) (f : k ⟶ i) (g : k ⟶ j),
      ∃ (l : C) (p : i ⟶ l) (q : j ⟶ l),
        IsPushout (CommRingCat.ofHom (F.map f).hom.toRingHom)
          (CommRingCat.ofHom (F.map g).hom.toRingHom)
          (CommRingCat.ofHom (F.map p).hom.toRingHom)
          (CommRingCat.ofHom (F.map q).hom.toRingHom)) :
    ((D.op ⋙ algSpec (.of R) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected := by
  apply specs_locallyDirected D
  intro i j k f g
  obtain ⟨l, p, q, h⟩ := hrefine i j k f g
  exact ⟨l, p, q, hretain k i j l f g p q h⟩

private def ambient_cocone {Y : Scheme.{u}} {T K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (base : Y ⟶ Spec (.of K)) (U : T → Y.Opens) (hU : ∀ t, IsAffineOpen (U t)) :
    Cocone (((intersectionIndexMap (id : T → T)) ⋙
      intersectionCoordinates base (intersectionOpens U)).op ⋙ algSpec (.of K)) :=
  (intersectionCoordinateCocone base U hU).whisker (intersectionIndexMap (id : T → T)).op

private def ambient_colimit {Y : Scheme.{u}} {T K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (base : Y ⟶ Spec (.of K)) (U : T → Y.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (hcover : (⨆ t, U t) = ⊤) : IsColimit (ambient_cocone base U hU) := by
  let E : (intersectionIndexMap (id : T → T)).op ≅
      𝟭 ({s : Finset T // s.Nonempty}ᵒᵖ) :=
    NatIso.op (index_iso T).symm ≪≫ Functor.opId {s : Finset T // s.Nonempty}
  let e := (CategoryTheory.Equivalence.refl
    (C := {s : Finset T // s.Nonempty}ᵒᵖ)).changeFunctor E.symm
  exact (coordinateCoconeIsColimit base U hU hcover).whiskerEquivalence e

private def closed_cocone {X Y : Scheme.{u}} {T K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (j : X ⟶ Y) [IsClosedImmersion j] (base : Y ⟶ Spec (.of K))
    (U : T → Y.Opens) (hU : ∀ t, IsAffineOpen (U t)) :
    Cocone ((intersectionCoordinates (j ≫ base) (intersectionOpens (fun t => j ⁻¹ᵁ U t))).op ⋙
      algSpec (.of K)) :=
  intersectionCoordinateCocone (j ≫ base) (fun t => j ⁻¹ᵁ U t)
    (fun t => (hU t).preimage j)

private def coordinate_inclusion {X Y : Scheme.{u}} {T K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (j : X ⟶ Y) [IsClosedImmersion j] (base : Y ⟶ Spec (.of K))
    (U : T → Y.Opens) (hU : ∀ t, IsAffineOpen (U t)) :
    (closed_cocone j base U hU).pt ⟶ (ambient_cocone base U hU).pt :=
  Over.homMk j rfl

private theorem coordinate_inclusion_legs {X Y : Scheme.{u}} {T K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (j : X ⟶ Y) [IsClosedImmersion j] (base : Y ⟶ Spec (.of K))
    (U : T → Y.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (s : {s : Finset T // s.Nonempty}ᵒᵖ) :
    (closed_cocone j base U hU).ι.app s ≫ coordinate_inclusion j base U hU =
      (algSpec (.of K)).map ((intersectionCoordinateMap j base
        (fun t => j ⁻¹ᵁ U t) U id (fun _ => le_rfl)).app s.unop).op ≫
        (ambient_cocone base U hU).ι.app s :=
  coordinateCocone_map j base (fun t => j ⁻¹ᵁ U t) U
    (fun t => (hU t).preimage j) hU id (fun _ => le_rfl) s

private def coordinate_claim
    {Y : Scheme.{u}} {T I K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (X : I → Scheme.{u}) [∀ i, IsAffineHom (pullback.diagonal (terminal.from (X i)))]
    (j : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (j i)]
    (base : Y ⟶ Spec (.of K)) (U : T → Y.Opens) (hU : ∀ t, IsAffineOpen (U t)) : Prop :=
  let C := {s : Finset T // s.Nonempty}
  let H₀ := intersectionIndexMap (id : T → T)
  let H : (Σ _ : I, C) ⥤ C := Sigma.desc (fun _ => H₀)
  let F := intersectionCoordinates base (intersectionOpens U)
  let B := fun i => intersectionCoordinates (j i ≫ base) (intersectionOpens (fun t => j i ⁻¹ᵁ U t))
  let A := (Sigma.desc B).sum' F
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
    (∀ x, Function.Surjective (β.app x).hom) →
    (∀ x y (a : x ⟶ y), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map a).hom.toRingHom))) →
    (∀ (x y z t) (a : x ⟶ y) (b : x ⟶ z) (p : y ⟶ t) (q : z ⟶ t),
      IsPushout (CommRingCat.ofHom (A.map a).hom.toRingHom)
        (CommRingCat.ofHom (A.map b).hom.toRingHom)
        (CommRingCat.ofHom (A.map p).hom.toRingHom)
        (CommRingCat.ofHom (A.map q).hom.toRingHom) →
      IsPushout (CommRingCat.ofHom (N.map a).hom.toRingHom)
        (CommRingCat.ofHom (N.map b).hom.toRingHom)
        (CommRingCat.ofHom (N.map p).hom.toRingHom)
        (CommRingCat.ofHom (N.map q).hom.toRingHom)) →
    (∀ i, (Functor.whiskerRight (NatTrans.op (quotient_component H₀ N β i))
      (algSpec (.of S) ⋙ Over.forget _)).Equifibered) →
    let F₀ := H₀ ⋙ (Sum.inr_ _ _ ⋙ N)
    let B₀ := fun i => Sigma.incl (C := fun _ : I => C) i ⋙ (Sum.inl_ _ _ ⋙ N)
    let eF := fun c => e (.inr (H₀.obj c))
    let eB := fun i c => e (.inl ⟨i, c⟩)
    ∀ (P : Over (Spec (.of S))) [CompactSpace P.left] [QuasiSeparatedSpace P.left]
      [LocallyOfFinitePresentation P.hom] (qP : Y ⟶ P.left)
      (hP : IsPullback qP base P.hom
        (Spec.map (CommRingCat.ofHom (algebraMap S K)))) (start : CoefficientStage S),
      ∃ (hnF : ∀ c d (a : c ⟶ d), (eF d).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (F₀.map a).hom) =
        ((H₀ ⋙ F).map a).hom.comp (eF c).toAlgHom)
        (hnB : ∀ i c d (a : c ⟶ d), (eB i d).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K ((B₀ i).map a).hom) =
        ((B i).map a).hom.comp (eB i c).toAlgHom),
      target_result S F₀ B₀ (quotient_component H₀ N β) (H₀ ⋙ F) B eF eB hnF hnB
        (ambient_cocone base U hU) (fun i => closed_cocone (j i) base U hU)
        (fun i => coordinate_inclusion (j i) base U hU) P qP hP start

private theorem construct_coordinate_targets
    {Y : Scheme.{u}} {T I K : Type u} [CommRing K] [Finite T]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (X : I → Scheme.{u}) [∀ i, IsAffineHom (pullback.diagonal (terminal.from (X i)))]
    (j : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (j i)]
    (base : Y ⟶ Spec (.of K)) (U : T → Y.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (hcover : (⨆ t, U t) = ⊤) : coordinate_claim X j base U hU := by
  classical
  dsimp only [coordinate_claim]
  intro S N e β hS hfp hn hβ hsurj hopen hpush hcart P _ _ _ qP hP start
  let C := {s : Finset T // s.Nonempty}
  let H₀ := intersectionIndexMap (id : T → T)
  let F := intersectionCoordinates base (intersectionOpens U)
  let B := fun i => intersectionCoordinates (j i ≫ base) (intersectionOpens (fun t => j i ⁻¹ᵁ U t))
  let Fbase := Sum.inr_ (Σ _ : I, C) C ⋙ N
  let F₀ := H₀ ⋙ Fbase
  let B₀ := fun i => Sigma.incl (C := fun _ : I => C) i ⋙
    (Sum.inl_ (Σ _ : I, C) C ⋙ N)
  let eF := fun c => e (.inr (H₀.obj c))
  let eB := fun i c => e (.inl ⟨i, c⟩)
  have hnF : ∀ c d (a : c ⟶ d), (eF d).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (F₀.map a).hom) =
      ((H₀ ⋙ F).map a).hom.comp (eF c).toAlgHom :=
    fun c d a => hn _ _ ((Sum.inr_ (Σ _ : I, C) C).map (H₀.map a))
  have hnB : ∀ i c d (a : c ⟶ d), (eB i d).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K ((B₀ i).map a).hom) =
      ((B i).map a).hom.comp (eB i c).toAlgHom :=
    fun i c d a => hn _ _ ((Sum.inl_ (Σ _ : I, C) C).map (Sigma.SigmaHom.mk a))
  let (c : C) : Algebra.FinitePresentation S (F₀.obj c) := hfp (.inr (H₀.obj c))
  let (i : I) (c : C) : Algebra.FinitePresentation S ((B₀ i).obj c) := hfp (.inl ⟨i, c⟩)
  let {c d : C} (a : c ⟶ d) : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F₀.map a).hom.toRingHom)) :=
    hopen _ _ ((Sum.inr_ (Σ _ : I, C) C).map (H₀.map a))
  have hretained := fun (c d f g : C) (a : c ⟶ d) (b : c ⟶ f)
      (p : d ⟶ g) (q : f ⟶ g) => hpush (.inr c) (.inr d) (.inr f) (.inr g)
      ((Sum.inr_ (Σ _ : I, C) C).map a) ((Sum.inr_ (Σ _ : I, C) C).map b)
      ((Sum.inr_ (Σ _ : I, C) C).map p) ((Sum.inr_ (Σ _ : I, C) C).map q)
  have hrefine (c d f : C) (a : f ⟶ c) (b : f ⟶ d) :
      ∃ (g : C) (p : c ⟶ g) (q : d ⟶ g),
      IsPushout (CommRingCat.ofHom (F.map a).hom.toRingHom)
        (CommRingCat.ofHom (F.map b).hom.toRingHom)
        (CommRingCat.ofHom (F.map p).hom.toRingHom)
        (CommRingCat.ofHom (F.map q).hom.toRingHom) := by
    obtain ⟨g, p, q, h⟩ := intersectionCoordinates_refine base U hU (op c) (op d) (op f)
      a.op b.op
    exact ⟨g.unop, p.unop, q.unop, h⟩
  let : ((Fbase.op ⋙ algSpec (.of S) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected :=
    retain_refinements Fbase F hretained hrefine
  let : ((F₀.op ⋙ algSpec (.of S) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected :=
    reindex_directed H₀ (index_identity T) Fbase
  refine ⟨hnF, hnB, ?_⟩
  exact exists_prefix_targets S hS F₀ B₀ (H₀ ⋙ F) B eF eB hnF hnB
    (quotient_component H₀ N β)
    (fun i => intersectionCoordinateMap (j i) base (fun t => j i ⁻¹ᵁ U t) U id
      (fun _ => le_rfl))
    (fun i c => hβ ⟨i, c⟩) hcart
    (fun i c => IsClosedImmersion.spec_of_surjective _ (hsurj ⟨i, c⟩))
    (ambient_cocone base U hU) (ambient_colimit base U hU hcover)
    (fun i => closed_cocone (j i) base U hU)
    (fun i => coordinateCoconeIsColimit (j i ≫ base) (fun t => j i ⁻¹ᵁ U t)
      (fun t => (hU t).preimage (j i)) ((j i).iSup_preimage_eq_top hcover))
    (fun i => coordinate_inclusion (j i) base U hU)
    (fun i c => coordinate_inclusion_legs (j i) base U hU c) P qP hP start

private theorem affine_diagonal (X : Scheme.{u}) [IsSeparated (terminal.from X)] :
    IsAffineHom (pullback.diagonal (terminal.from X)) := by
  let : IsClosedImmersion (pullback.diagonal (terminal.from X)) :=
    IsSeparated.isClosedImmersion_diagonal (f := terminal.from X)
  infer_instance

private theorem variety_diagonal {K : Type u} [Field K] (V : GroupActions.Variety K) :
    IsAffineHom (pullback.diagonal (terminal.from V.scheme)) := by
  let : IsSeparated (terminal.from V.scheme) := by
    rw [← terminal.comp_from V.toSpec]
    infer_instance
  exact affine_diagonal V.scheme

end SchubertGeometry
