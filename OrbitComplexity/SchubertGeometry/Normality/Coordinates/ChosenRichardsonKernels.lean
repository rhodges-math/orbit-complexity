import OrbitComplexity.SchubertGeometry.Normality.Coordinates.ChosenRichardsonClosed
import OrbitComplexity.SchubertGeometry.Normality.Coordinates.ChosenCoverRetractions
import OrbitComplexity.FrobeniusSplitting.Normality.Images.EndpointKernelTransport
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.FixedCoordinateCocone
import OrbitComplexity.FrobeniusSplitting.Normality.Models.ClosedChartQuotients
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Specialization of the prescribed Richardson endpoint ideal

The chart comparisons are obtained by restricting the original Cartesian
squares. All identifications of open restrictions and coordinate maps are
proved over arbitrary schemes before use on the chosen models.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting ReductiveGroups
open scoped TensorProduct

namespace SchubertGeometry

universe u

open private coordinates_finitePresentation
  from OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams
open private intersection_preimage
  from OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.FixedCoordinateCocone
open private preimage_intersection
  from OrbitComplexity.FrobeniusSplitting.Normality.Models.ClosedChartQuotients

private def singleton_index {I : Type u} (i : I) : {s : Finset I // s.Nonempty} :=
  ⟨{i}, Finset.singleton_nonempty i⟩

private theorem singleton_intersection_eq {X : Scheme.{u}} {I : Type u}
    (W : I → X.Opens) (i : I) :
    (intersectionOpens W).obj
      ((intersectionIndexMap id).op.obj (op (singleton_index i))) = W i := by
  classical
  change (⨅ t ∈ ({i} : Finset I).image id, W t) = W i
  rw [Finset.image_id, ← Finset.inf_eq_iInf, Finset.inf_singleton]

private theorem comp_restricted_ι {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (W : Y.Opens) (q : Z ⟶ (f ⁻¹ᵁ W).toScheme) :
    (q ≫ (f ⁻¹ᵁ W).ι) ≫ f = (q ≫ (f ∣_ W)) ≫ W.ι := by
  exact (Category.assoc q _ f).trans
    ((congrArg (fun a => q ≫ a) (morphismRestrict_ι f W).symm).trans
      (Category.assoc q (f ∣_ W) W.ι).symm)

private theorem chosen_intersection_preimages
    {D₀ F₀ D F : Scheme.{u}} {I : Type u}
    (j₀ : D₀ ⟶ F₀) (j : D ⟶ F) (qD : D ⟶ D₀) (qF : F ⟶ F₀)
    (h : qD ≫ j₀ = j ≫ qF) (W : I → F₀.Opens)
    (s : {s : Finset I // s.Nonempty}) :
    let W₀ := (intersectionOpens W).obj ((intersectionIndexMap id).op.obj (op s))
    let V := (intersectionOpens (fun i => qF ⁻¹ᵁ W i)).obj
      ((intersectionIndexMap id).op.obj (op s))
    let U := (intersectionOpens (fun i => j ⁻¹ᵁ (qF ⁻¹ᵁ W i))).obj (op s)
    V = qF ⁻¹ᵁ W₀ ∧ U = qD ⁻¹ᵁ (j₀ ⁻¹ᵁ W₀) := by
  dsimp only
  have hV := (intersection_preimage qF W
    ((intersectionIndexMap id).op.obj (op s))).symm
  refine ⟨hV, ?_⟩
  exact (preimage_intersection j (fun i => qF ⁻¹ᵁ W i) (op s)).trans
    ((congrArg (fun A : F.Opens => j ⁻¹ᵁ A) hV).trans
      (endpoint_preimage_eq j₀ j qD qF h _).symm)

private theorem restricted_inclusion_square
    {B T D₀ F₀ D F : Scheme.{u}} (ρ : T ⟶ B)
    (d₀ : D₀ ⟶ B) (f₀ : F₀ ⟶ B) (d : D ⟶ T) (f : F ⟶ T)
    (j₀ : D₀ ⟶ F₀) (j : D ⟶ F)
    (hj₀ : j₀ ≫ f₀ = d₀) (hj : j ≫ f = d)
    (qD : D ⟶ D₀) (qF : F ⟶ F₀)
    (hD : IsPullback qD d d₀ ρ) (hF : IsPullback qF f f₀ ρ)
    (hsquare : qD ≫ j₀ = j ≫ qF) (W : F₀.Opens) :
    let U₀ := j₀ ⁻¹ᵁ W
    let V := qF ⁻¹ᵁ W
    let U := j ⁻¹ᵁ V
    ∃ qDU : U.toScheme ⟶ U₀.toScheme,
      IsPullback qDU (U.ι ≫ d) (U₀.ι ≫ d₀) ρ ∧
      IsPullback (qF ∣_ W) (V.ι ≫ f) (W.ι ≫ f₀) ρ ∧
      qDU ≫ U₀.ι = U.ι ≫ qD ∧
      (j ∣_ V) ≫ (qF ∣_ W) = qDU ≫ (j₀ ∣_ W) ∧
      (j₀ ∣_ W) ≫ (W.ι ≫ f₀) = U₀.ι ≫ d₀ ∧
      (j ∣_ V) ≫ (V.ι ≫ f) = U.ι ≫ d := by
  let U₀ := j₀ ⁻¹ᵁ W
  let V := qF ⁻¹ᵁ W
  let U := j ⁻¹ᵁ V
  have hU : U = qD ⁻¹ᵁ U₀ :=
    (endpoint_preimage_eq j₀ j qD qF hsquare W).symm
  let qDU := qD.resLE U₀ U (le_of_eq hU)
  have hqDU : qDU ≫ U₀.ι = U.ι ≫ qD :=
    Scheme.Hom.resLE_comp_ι _ _
  have hchart : (j ∣_ V) ≫ (qF ∣_ W) = qDU ≫ (j₀ ∣_ W) := by
    apply (cancel_mono W.ι).1
    calc
      ((j ∣_ V) ≫ (qF ∣_ W)) ≫ W.ι =
          (j ∣_ V) ≫ (V.ι ≫ qF) := by
            rw [Category.assoc, morphismRestrict_ι]
      _ = (U.ι ≫ j) ≫ qF := by
        rw [← Category.assoc, morphismRestrict_ι]
      _ = U.ι ≫ (qD ≫ j₀) := by rw [Category.assoc, ← hsquare]
      _ = (qDU ≫ U₀.ι) ≫ j₀ := by rw [hqDU, Category.assoc]
      _ = (qDU ≫ (j₀ ∣_ W)) ≫ W.ι := by
        exact comp_restricted_ι j₀ W qDU
  have hbase₀ : (j₀ ∣_ W) ≫ (W.ι ≫ f₀) = U₀.ι ≫ d₀ := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hj₀]
  have hbase : (j ∣_ V) ≫ (V.ι ≫ f) = U.ι ≫ d := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hj]
  exact ⟨qDU, restriction_scalar_square ρ d₀ d qD hD U₀ U hU,
    (isPullback_morphismRestrict qF W).paste_vert hF,
    hqDU, hchart, hbase₀, hbase⟩

private theorem restricted_graph_square
    {B T D₀ F₀ D F : Scheme.{u}} (ρ : T ⟶ B)
    (d₀ : D₀ ⟶ B) (f₀ : F₀ ⟶ B) (d : D ⟶ T) (f : F ⟶ T)
    (j₀ : D₀ ⟶ F₀) (j : D ⟶ F)
    (hj₀ : j₀ ≫ f₀ = d₀) (hj : j ≫ f = d)
    (qD : D ⟶ D₀) (qF : F ⟶ F₀)
    (hD : IsPullback qD d d₀ ρ) (hF : IsPullback qF f f₀ ρ)
    (hsquare : qD ≫ j₀ = j ≫ qF)
    (W : F₀.Opens) (V : F.Opens) (U : D.Opens)
    (hV : V = qF ⁻¹ᵁ W) (hU : U = qD ⁻¹ᵁ (j₀ ⁻¹ᵁ W))
    (r : U.toScheme ⟶ V.toScheme) (hr : r ≫ V.ι = U.ι ≫ j) :
    let U₀ := j₀ ⁻¹ᵁ W
    ∃ (qDU : U.toScheme ⟶ U₀.toScheme) (qFV : V.toScheme ⟶ W.toScheme),
      IsPullback qDU (U.ι ≫ d) (U₀.ι ≫ d₀) ρ ∧
      IsPullback qFV (V.ι ≫ f) (W.ι ≫ f₀) ρ ∧
      qDU ≫ U₀.ι = U.ι ≫ qD ∧ qFV ≫ W.ι = V.ι ≫ qF ∧
      r ≫ qFV = qDU ≫ (j₀ ∣_ W) ∧
      (j₀ ∣_ W) ≫ (W.ι ≫ f₀) = U₀.ι ≫ d₀ ∧
      r ≫ (V.ι ≫ f) = U.ι ≫ d := by
  let U₀ := j₀ ⁻¹ᵁ W
  let qDU := qD.resLE U₀ U (le_of_eq hU)
  let qFV := qF.resLE W V (le_of_eq hV)
  have hqDU : qDU ≫ U₀.ι = U.ι ≫ qD := Scheme.Hom.resLE_comp_ι _ _
  have hqFV : qFV ≫ W.ι = V.ι ≫ qF := Scheme.Hom.resLE_comp_ι _ _
  have hchart : r ≫ qFV = qDU ≫ (j₀ ∣_ W) := by
    apply (cancel_mono W.ι).1
    calc
      (r ≫ qFV) ≫ W.ι = (r ≫ V.ι) ≫ qF := by
        rw [Category.assoc, hqFV, ← Category.assoc]
      _ = (U.ι ≫ j) ≫ qF := by rw [hr]
      _ = U.ι ≫ (qD ≫ j₀) := by rw [Category.assoc, ← hsquare]
      _ = (qDU ≫ U₀.ι) ≫ j₀ := by rw [hqDU, Category.assoc]
      _ = (qDU ≫ (j₀ ∣_ W)) ≫ W.ι := by
        exact comp_restricted_ι j₀ W qDU
  have hbase₀ : (j₀ ∣_ W) ≫ (W.ι ≫ f₀) = U₀.ι ≫ d₀ := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hj₀]
  have hbase : r ≫ (V.ι ≫ f) = U.ι ≫ d := by
    rw [← Category.assoc, hr, Category.assoc, hj]
  exact ⟨qDU, qFV, restriction_scalar_square ρ d₀ d qD hD U₀ U hU,
    restriction_scalar_square ρ f₀ f qF hF W V hV,
    hqDU, hqFV, hchart, hbase₀, hbase⟩

private theorem chosen_intersection_square
    {B D₀ F₀ D F : Scheme.{u}} {I K : Type u} [CommRing K]
    (ρ : Spec (.of K) ⟶ B) (d₀ : D₀ ⟶ B) (f₀ : F₀ ⟶ B)
    (f : F ⟶ Spec (.of K)) (j₀ : D₀ ⟶ F₀) (j : D ⟶ F)
    (hj₀ : j₀ ≫ f₀ = d₀)
    (qD : D ⟶ D₀) (qF : F ⟶ F₀)
    (hD : IsPullback qD (j ≫ f) d₀ ρ)
    (hF : IsPullback qF f f₀ ρ)
    (hsquare : qD ≫ j₀ = j ≫ qF)
    (W : I → F₀.Opens) (s : {s : Finset I // s.Nonempty}) :
    let W₀ := (intersectionOpens W).obj ((intersectionIndexMap id).op.obj (op s))
    let V := (intersectionOpens (fun i => qF ⁻¹ᵁ W i)).obj
      ((intersectionIndexMap id).op.obj (op s))
    let U := (intersectionOpens (fun i => j ⁻¹ᵁ (qF ⁻¹ᵁ W i))).obj (op s)
    let r : U.toScheme ⟶ V.toScheme :=
      ((intersectionSchemeMap j f (fun i => j ⁻¹ᵁ (qF ⁻¹ᵁ W i))
        (fun i => qF ⁻¹ᵁ W i) id (fun _ => le_rfl)).app (op s)).left
    ∃ (qDU : U.toScheme ⟶ (j₀ ⁻¹ᵁ W₀).toScheme)
      (qFV : V.toScheme ⟶ W₀.toScheme),
      IsPullback qDU (U.ι ≫ (j ≫ f)) ((j₀ ⁻¹ᵁ W₀).ι ≫ d₀) ρ ∧
      IsPullback qFV (V.ι ≫ f) (W₀.ι ≫ f₀) ρ ∧
      qDU ≫ (j₀ ⁻¹ᵁ W₀).ι = U.ι ≫ qD ∧
      qFV ≫ W₀.ι = V.ι ≫ qF ∧
      r ≫ qFV = qDU ≫ (j₀ ∣_ W₀) ∧
      (j₀ ∣_ W₀) ≫ (W₀.ι ≫ f₀) = (j₀ ⁻¹ᵁ W₀).ι ≫ d₀ ∧
      r ≫ (V.ι ≫ f) = U.ι ≫ (j ≫ f) := by
  let W₀ := (intersectionOpens W).obj ((intersectionIndexMap id).op.obj (op s))
  let V := (intersectionOpens (fun i => qF ⁻¹ᵁ W i)).obj
    ((intersectionIndexMap id).op.obj (op s))
  let U := (intersectionOpens (fun i => j ⁻¹ᵁ (qF ⁻¹ᵁ W i))).obj (op s)
  let r : U.toScheme ⟶ V.toScheme :=
    ((intersectionSchemeMap j f (fun i => j ⁻¹ᵁ (qF ⁻¹ᵁ W i))
      (fun i => qF ⁻¹ᵁ W i) id (fun _ => le_rfl)).app (op s)).left
  have hr : r ≫ V.ι = U.ι ≫ j := Scheme.Hom.resLE_comp_ι _ _
  obtain ⟨hV, hU⟩ := chosen_intersection_preimages j₀ j qD qF hsquare W s
  exact restricted_graph_square ρ d₀ f₀ (j ≫ f) f
    j₀ j hj₀ rfl qD qF hD hF hsquare W₀ V U hV hU r hr

private theorem restricted_endpoint_square {R K : Type u}
    [CommRing R] [CommRing K] [Algebra R K]
    {X₀ Y₀ X Y : Scheme.{u}}
    (x₀ : X₀ ⟶ Spec (.of R)) (y₀ : Y₀ ⟶ Spec (.of R))
    (x : X ⟶ Spec (.of K)) (y : Y ⟶ Spec (.of K))
    (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y)
    (hf₀ : f₀ ≫ y₀ = x₀) (hf : f ≫ y = x)
    [QuasiCompact f] [Surjective f]
    (qX : X ⟶ X₀) (qY : Y ⟶ Y₀)
    (hX : IsPullback qX x x₀
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hY : IsPullback qY y y₀
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hsquare : qX ≫ f₀ = f ≫ qY) (W : Y₀.Opens) :
    let U₀ := f₀ ⁻¹ᵁ W
    let V := qY ⁻¹ᵁ W
    let U := qX ⁻¹ᵁ U₀
    ∃ fK : U.toScheme ⟶ V.toScheme,
      IsPullback (qX ∣_ U₀) (U.ι ≫ x) (U₀.ι ≫ x₀)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      IsPullback (qY ∣_ W) (V.ι ≫ y) (W.ι ≫ y₀)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      (f₀ ∣_ W) ≫ (W.ι ≫ y₀) = U₀.ι ≫ x₀ ∧
      fK ≫ (V.ι ≫ y) = U.ι ≫ x ∧
      fK ≫ (qY ∣_ W) = (qX ∣_ U₀) ≫ (f₀ ∣_ W) ∧
      fK ≫ V.ι = U.ι ≫ f ∧ QuasiCompact fK ∧ Surjective fK := by
  let U₀ := f₀ ⁻¹ᵁ W
  let V := qY ⁻¹ᵁ W
  let U := qX ⁻¹ᵁ U₀
  have hU : U = f ⁻¹ᵁ V := endpoint_preimage_eq f₀ f qX qY hsquare W
  let EU : X.restrictFunctor.obj U ≅ X.restrictFunctor.obj (f ⁻¹ᵁ V) :=
    X.restrictFunctor.mapIso (eqToIso hU)
  let a : U.toScheme ⟶ (f ⁻¹ᵁ V).toScheme := EU.hom.left
  have ha : a ≫ (f ⁻¹ᵁ V).ι = U.ι := EU.hom.w
  let fK : U.toScheme ⟶ V.toScheme := a ≫ (f ∣_ V)
  have hfKι : fK ≫ V.ι = U.ι ≫ f := by
    change (a ≫ (f ∣_ V)) ≫ V.ι = _
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, ha]
  have hK : fK ≫ (V.ι ≫ y) = U.ι ≫ x := by
    rw [← Category.assoc, hfKι, Category.assoc, hf]
  have h₀ : (f₀ ∣_ W) ≫ (W.ι ≫ y₀) = U₀.ι ≫ x₀ := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hf₀]
  have hchart : fK ≫ (qY ∣_ W) = (qX ∣_ U₀) ≫ (f₀ ∣_ W) := by
    apply (cancel_mono W.ι).1
    calc
      (fK ≫ (qY ∣_ W)) ≫ W.ι = fK ≫ (V.ι ≫ qY) := by
        rw [Category.assoc, morphismRestrict_ι]
      _ = (U.ι ≫ f) ≫ qY := by rw [← Category.assoc, hfKι]
      _ = U.ι ≫ (qX ≫ f₀) := by rw [Category.assoc, ← hsquare]
      _ = ((qX ∣_ U₀) ≫ U₀.ι) ≫ f₀ := by
        rw [morphismRestrict_ι, Category.assoc]
      _ = ((qX ∣_ U₀) ≫ (f₀ ∣_ W)) ≫ W.ι := by
        exact comp_restricted_ι f₀ W (qX ∣_ U₀)
  let : IsIso a := inferInstanceAs (IsIso ((Over.forget X).map EU.hom))
  let : Surjective (f ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f V).flip inferInstance
  have hqc : QuasiCompact fK := inferInstanceAs (QuasiCompact (a ≫ (f ∣_ V)))
  have hsurj : Surjective fK := inferInstanceAs (Surjective (a ≫ (f ∣_ V)))
  exact ⟨fK, (isPullback_morphismRestrict qX U₀).paste_vert hX,
    (isPullback_morphismRestrict qY W).paste_vert hY, h₀, hK, hchart,
    hfKι, hqc, hsurj⟩

set_option maxHeartbeats 400000 in
private theorem chosen_patch_retraction {K : Type u} [Field K]
    (S : Subalgebra ℤ K) (hS : S.FG)
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
    (hsquare : qX ≫ f₀ = f ≫ qY) (W : Y₀.Opens) (hW : IsAffineOpen W) :
    let U₀ := f₀ ⁻¹ᵁ W
    let sourceBase := U₀.ι ≫ x₀
    let targetBase := W.ι ≫ y₀
    let source := Over.mk sourceBase
    let target := Over.mk targetBase
    let fR : source ⟶ target := Over.homMk (f₀ ∣_ W) (by
      change (f₀ ∣_ W) ≫ (W.ι ≫ y₀) = U₀.ι ≫ x₀
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hf₀])
    ∃ V : U₀.toScheme.OpenCover.{u},
      Finite V.I₀ ∧ (∀ j, IsAffine (V.X j)) ∧
      ∃ (R : Subalgebra ℤ K), R.FG ∧ ∃ hSR : S ≤ R,
        let _ : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
        ∃ r : R ⊗[S] (∀ j, ((algΓ (.of S)).obj
          (Over.mk (V.f j ≫ sourceBase))).unop) →ₗ[R]
            R ⊗[S] ((algΓ (.of S)).obj target).unop,
          r.comp (Algebra.TensorProduct.lTensor (S := R) R
            (affineCoverSectionMap fR V)).toLinearMap = LinearMap.id := by
  let U₀ := f₀ ⁻¹ᵁ W
  let VY := qY ⁻¹ᵁ W
  let VX := qX ⁻¹ᵁ U₀
  let sourceBase := U₀.ι ≫ x₀
  let targetBase := W.ι ≫ y₀
  let sourceKBase := VX.ι ≫ x
  let targetKBase := VY.ι ≫ y
  let : IsAffine W.toScheme := hW
  let : CompactSpace U₀.toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (f₀ ∣_ W)
  let V := U₀.toScheme.affineCover.finiteSubcover
  have hV (j : V.I₀) : IsAffine (V.X j) := by
    change IsAffine (U₀.toScheme.affineCover.X _)
    infer_instance
  obtain ⟨fK, hXK, hYK, hR, hK, hchart, _hfKι, hqc, hsurj⟩ :=
    restricted_endpoint_square x₀ y₀ x y f₀ f hf₀ hf qX qY hX hY hsquare W
  let : QuasiCompact fK := hqc
  let : Surjective fK := hsurj
  let : IsReduced VY.toScheme := inferInstance
  let : LocallyOfFinitePresentation sourceBase := by
    change LocallyOfFinitePresentation (U₀.ι ≫ x₀)
    infer_instance
  let : LocallyOfFinitePresentation targetBase := by
    change LocallyOfFinitePresentation (W.ι ≫ y₀)
    infer_instance
  let : Algebra.FinitePresentation S
      ((algΓ (.of S)).obj (Over.mk targetBase)).unop :=
    @coordinates_finitePresentation (.of S) (Over.mk targetBase)
      (inferInstanceAs (IsAffine W.toScheme))
      (inferInstanceAs (LocallyOfFinitePresentation targetBase))
  let (j : V.I₀) : IsAffine (V.X j) := hV j
  let (j : V.I₀) : LocallyOfFinitePresentation (V.f j ≫ sourceBase) :=
    inferInstance
  let (j : V.I₀) : Algebra.FinitePresentation S
      ((algΓ (.of S)).obj (Over.mk (V.f j ≫ sourceBase))).unop :=
    @coordinates_finitePresentation (.of S) (Over.mk (V.f j ≫ sourceBase))
      (hV j) (inferInstanceAs (LocallyOfFinitePresentation (V.f j ≫ sourceBase)))
  obtain ⟨R, hRfg, hSR, r, hr⟩ := exists_chosen_cover_retractions S hS
    sourceBase targetBase sourceKBase targetKBase (f₀ ∣_ W) fK hR hK
      (qX ∣_ U₀) (qY ∣_ W) hXK hYK hchart V hV
  exact ⟨V, inferInstance, hV, R, hRfg, hSR, r, hr⟩

private theorem endpoint_kernel_on_charts
    {S R A B O M Q A' M' P : Type u}
    [CommRing S] [CommRing R] [CommRing A] [CommRing B] [CommRing O]
    [CommRing M] [CommRing Q] [CommRing A'] [CommRing M'] [CommRing P]
    [Algebra S R] [Algebra S A] [Algebra S B] [Algebra S O]
    [Algebra S M] [Algebra S Q] [Algebra R A'] [Algebra R M'] [Algebra R P]
    (b : A →ₐ[S] B) (o : A →ₐ[S] O) (m : A →ₐ[S] M) (q : A →ₐ[S] Q)
    (hq : Function.Surjective q)
    (hkq : RingHom.ker q.toRingHom =
      RingHom.ker b.toRingHom ⊔ RingHom.ker o.toRingHom)
    (E : R ⊗[S] Q ≃ₐ[R] R ⊗[S] M)
    (hE : E.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := R) R q) =
      Algebra.TensorProduct.lTensor (S := R) R m)
    (θ : R ⊗[S] B →ₐ[R] R ⊗[S] M)
    (ω : R ⊗[S] O →ₐ[R] R ⊗[S] M)
    (hθ : θ.comp (Algebra.TensorProduct.lTensor (S := R) R b) =
      Algebra.TensorProduct.lTensor (S := R) R m)
    (hω : ω.comp (Algebra.TensorProduct.lTensor (S := R) R o) =
      Algebra.TensorProduct.lTensor (S := R) R m)
    (eA : R ⊗[S] A ≃ₐ[R] A') (eM : R ⊗[S] M ≃ₐ[R] M')
    (m' : A' →ₐ[R] M')
    (hm : eM.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := R) R m) =
      m'.comp eA.toAlgHom)
    (g : M' →ₐ[R] P) (r : P →ₗ[R] M')
    (hr : r.comp g.toLinearMap = LinearMap.id) :
    let b' := (Algebra.TensorProduct.lTensor (S := R) R b).comp eA.symm.toAlgHom
    let o' := (Algebra.TensorProduct.lTensor (S := R) R o).comp eA.symm.toAlgHom
    ∀ (L : Type u) [CommRing L] [Algebra R L],
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (g.comp m')).toRingHom =
        RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L b').toRingHom ⊔
        RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L o').toRingHom := by
  let b' := (Algebra.TensorProduct.lTensor (S := R) R b).comp eA.symm.toAlgHom
  let o' := (Algebra.TensorProduct.lTensor (S := R) R o).comp eA.symm.toAlgHom
  have hb : (AlgEquiv.refl : R ⊗[S] B ≃ₐ[R] R ⊗[S] B).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := R) R b) = b'.comp eA.toAlgHom := by
    apply AlgHom.ext
    intro x
    change Algebra.TensorProduct.lTensor (S := R) R b x =
      Algebra.TensorProduct.lTensor (S := R) R b (eA.symm (eA x))
    rw [eA.symm_apply_apply]
  have ho : (AlgEquiv.refl : R ⊗[S] O ≃ₐ[R] R ⊗[S] O).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := R) R o) = o'.comp eA.toAlgHom := by
    apply AlgHom.ext
    intro x
    change Algebra.TensorProduct.lTensor (S := R) R o x =
      Algebra.TensorProduct.lTensor (S := R) R o (eA.symm (eA x))
    rw [eA.symm_apply_apply]
  dsimp only
  intro L _ _
  exact endpoint_sum_kernel_transport (F := L) b o m q hq hkq E hE θ ω hθ hω
    eA (AlgEquiv.refl : R ⊗[S] B ≃ₐ[R] R ⊗[S] B)
    (AlgEquiv.refl : R ⊗[S] O ≃ₐ[R] R ⊗[S] O) eM
    b' o' m' hb ho hm g r hr


end SchubertGeometry
