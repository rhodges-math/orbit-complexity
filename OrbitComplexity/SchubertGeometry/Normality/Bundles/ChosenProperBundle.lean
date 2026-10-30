import OrbitComplexity.SchubertGeometry.Normality.Transitions.ChosenBorelTransitions
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarDiagramComparison
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.FixedCoordinateProjection
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.CoordinateDiagramOpens
import OrbitComplexity.SchubertGeometry.Normality.Bundles.BorelModelBundle
import Batteries.Tactic.Lint

/-! # Projective bundles on the proper prior model -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u
namespace SchubertGeometry

private theorem intersection_smooth {S : Type u} [CommRing S] {Y : Scheme.{u}}
    [Y.IsSeparated] (base : Y ⟶ Spec (.of S)) [Smooth base] {I : Type u}
    (U : I → Y.Opens) (hU : ∀ j, IsAffineOpen (U j))
    (s : {s : Finset I // s.Nonempty}) :
    Algebra.Smooth S ((intersectionCoordinates base (intersectionOpens U)).obj s) := by
  let X := ((intersectionOpens U).obj (.op s)).toScheme
  let f : X ⟶ Spec (.of S) := ((intersectionOpens U).obj (.op s)).ι ≫ base
  have : IsAffine X := intersectionOpens_affine U hU (.op s)
  have : Smooth f := by dsimp only [f]; infer_instance
  change ((f.appTop).hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).Smooth
  exact (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of S)).inv)).comp
      (HasRingHomProperty.appTop (P := @Smooth) f inferInstance)

private theorem bundle_of_parameters {I R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), F.obj s)
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG)
    (H : modelProjectiveSpec N F e sel c a) : modelBundleSpec N F e sel c a cG := by
  obtain ⟨c0, a0, hc, ha, hco, hn, D, eP, π, hproj, hmap, hcart⟩ := H
  exact ⟨c0, a0, hc, ha, hco, hn, D, eP, π, hproj, hmap, hcart,
    exists_projective_bundle N D π hcart (fun s ↦ eP s.unop)
      (fun s ↦ hproj s.unop) cG hcG⟩

private theorem projective_of_lifts {I R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (hv : ∀ s x, e s ((1 : K) ⊗ₜ[R] x) = (v.app s).hom x)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), F.obj s)
    (H : transitionLiftSpec N F v c a) : modelProjectiveSpec N F e sel c a := by
  obtain ⟨c0, a0, hc, ha, hco, hn⟩ := H
  exact ⟨c0, a0, (fun s j hj k hk ↦ (hv s _).trans (hc s j hj k hk)),
    (fun s j hj k hk ↦ (hv s _).trans (ha s j hj k hk)), hco, hn,
    exists_projective_transition N sel c0 a0 hco hn⟩

private theorem fixed_parameters {K : Type u} [kField : Field K] {I : Type u}
    (S R : Subalgebra ℤ K) (hSR : S ≤ R)
    (M : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), F.obj s) :
    letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
    letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
    let N := fixedFibreDiagram (R := R) (M := R) M
    let eR := @scalarDiagramComparison.{u,u,u} K kField S R hSR
      {s : Finset I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e
    ∀ (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
        F ⋙ forget₂ (CommAlgCat K) CommRingCat)
      (_hv : ∀ s x, (v.app s).hom x = e s
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S (M.obj s)) x))
      (_H : transitionLiftSpec N F v c a),
    (∀ s t (f : s ⟶ t), (eR t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
        (F.map f).hom.comp (eR s).toAlgHom) ∧
    modelProjectiveSpec N F eR sel c a := by
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  intro N eR v hv H
  have heR := @scalarDiagramComparison_natural.{u,u,u} K kField S R hSR
    {s : Finset I // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e he
  have hval (s : {s : Finset I // s.Nonempty}) (x : N.obj s) :
      eR s ((1 : K) ⊗ₜ[R] x) = e s
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
          (AlgHom.id S (M.obj s)) x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
        change eR s ((1 : K) ⊗ₜ[R] (r ⊗ₜ[S] x)) =
          e s (algebraMap R K r ⊗ₜ[S] x)
        simpa only [mul_one] using
          @scalarDiagramComparison_tmul.{u,u,u} K kField S R hSR
            {s : Finset I // s.Nonempty}
            (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e s 1 r x
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  have hvR (s : {s : Finset I // s.Nonempty}) (x : N.obj s) :
      eR s ((1 : K) ⊗ₜ[R] x) = (v.app s).hom x :=
    (hval s x).trans (hv s x).symm
  exact ⟨heR, @projective_of_lifts.{u} I R K
    (inferInstanceAs (CommRing R)) (@Field.toCommRing K kField)
    (inferInstanceAs (Algebra R K)) N F eR v hvR sel c a H⟩

private def parameterSpec {K : Type u} [kField : Field K] {I : Type u}
    (S : Subalgebra ℤ K) (M : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), F.obj s) : Prop :=
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      let N := fixedFibreDiagram (R := R) (M := R) M
      let eR := @scalarDiagramComparison.{u,u,u} K kField S R hSR
        {s : Finset I // s.Nonempty}
        (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e
      R.FG ∧
      (∀ s t (f : s ⟶ t), (eR t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
          (F.map f).hom.comp (eR s).toAlgHom) ∧
      modelProjectiveSpec N F eR sel c a

private theorem convert_parameters {K : Type u} [kField : Field K] {I : Type u}
    (S : Subalgebra ℤ K) (M : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), F.obj s)
    (H : ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      let N := fixedFibreDiagram (R := R) (M := R) M
      ∃ v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
          F ⋙ forget₂ (CommAlgCat K) CommRingCat,
        R.FG ∧
        (∀ s x, (v.app s).hom x = e s
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
            (AlgHom.id S (M.obj s)) x)) ∧ transitionLiftSpec N F v c a) :
    parameterSpec S M F e sel c a := by
  unfold parameterSpec
  obtain ⟨R, hSR, H⟩ := H
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  obtain ⟨v, hR, hv, H⟩ := H
  have hfixed := @fixed_parameters.{u} K kField I S R hSR M F e he sel c a v hv H
  exact ⟨R, hSR, hR, hfixed⟩

private theorem chosen_parameters {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support) {I : Type u} [iFinite : Finite I]
    (S : Subalgebra ℤ K) (hS : S.FG)
    (M : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [mFP : ∀ s, Algebra.FinitePresentation S (M.obj s)]
    [mSmooth : ∀ s, Algebra.Smooth S (M.obj s)]
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (beta : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hnatural : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk) :
    let scale := fun s j hj k hk ↦ Units.map
      (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
        (simpleRootCoefficient G i)
    let shift := fun s j hj k hk ↦
      simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
        ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)
    parameterSpec S M F e sel scale shift := by
  let scale := fun s j hj k hk ↦ Units.map
    (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
      (simpleRootCoefficient G i)
  let shift := fun s j hj k hk ↦ simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
    ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)
  change parameterSpec S M F e sel scale shift
  exact @convert_parameters.{u} K kField I S M F e he sel scale shift
    (@exists_chosen_borel_transitions.{u,u} K kField kClosed kZero G i I iFinite
      S hS M mFP mSmooth F e he beta hnatural hbeta)

/- The Borel parameters descend on a coefficient pullback of the proper prior
scheme. Its chosen coordinate cocone and every comparison leg are retained. -/
variable {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base]
    {I : Type u} [iFinite : Finite I] (U : I → Y.Opens) (hU : ∀ j, IsAffineOpen (U j))
    (hcover : (⨆ j, U j) = ⊤)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] (intersectionCoordinates base (intersectionOpens U)).obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K ((intersectionCoordinates base (intersectionOpens
        U)).map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (beta : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hnatural : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk)

/-- The full same-prior bundle conclusion, including every canonical coordinate leg. -/
def chosenProperBundleSpec : Prop :=
    let scale := fun s j hj k hk ↦ Units.map
      (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
        (simpleRootCoefficient G i)
    let shift := fun s j hj k hk ↦
      simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
        ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      let M := intersectionCoordinates base (intersectionOpens U)
      let N := fixedFibreDiagram (R := R) (M := R) M
      let eR := @scalarDiagramComparison.{u,u,u} K kField S R hSR
        {s : Finset I // s.Nonempty}
        (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e
      let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
      let YR := pullback base sr
      let baseR := pullback.snd base sr
      let qR := pullback.fst base sr
      let B := intersectionOpens U
      let V : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ YR.Opens :=
        { obj := fun s ↦ qR ⁻¹ᵁ B.obj s
          map := fun f ↦ homOfLE (qR.preimage_mono (leOfHom (B.map f))) }
      let E := V ⋙ YR.restrictFunctor ⋙ Over.map baseR
      let C := (E ⋙ algΓ (.of R)).unop
      let vcoords : ∀ s, M.obj s →+* C.obj s :=
        fun s ↦ (qR ∣_ B.obj (.op s)).appTop.hom
      R.FG ∧
      (∀ s t (f : s ⟶ t), (eR t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
          (F.map f).hom.comp (eR s).toAlgHom) ∧
      ∃ (hE : ∀ s, IsAffine (E.obj s).left)
        (d : N ≅ C) (cG : Cocone (N.op ⋙ algSpec (.of R))),
        (∀ s r x, (d.hom.app s).hom (r ⊗ₜ[S] x) =
          algebraMap R (C.obj s) r * vcoords s x) ∧
        ∃ hpt : cG.pt = Over.mk baseR,
          Nonempty (IsColimit cG) ∧ IsProper cG.pt.hom ∧
          (∀ s, (cG.ι.app s ≫ eqToHom hpt).left =
            Spec.map (CommRingCat.ofHom (d.inv.app s.unop).hom.toRingHom) ≫
              (by letI := hE; exact ((coordinateDiagramIso (.of R) E).inv.app s).left) ≫
                (V.obj s).ι) ∧
          modelBundleSpec N F eR sel scale shift cG

include hS hU hcover he hnatural hbeta

/-- The regular Borel transitions construct a bundle on the proper prior pullback. -/
theorem exists_chosen_proper_bundle : chosenProperBundleSpec G i S base U F e sel beta := by
  unfold chosenProperBundleSpec
  classical
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from base]; infer_instance⟩
  let M := intersectionCoordinates base (intersectionOpens U)
  let (s : {s : Finset I // s.Nonempty}) : Algebra.Smooth S (M.obj s) :=
    intersection_smooth base U hU s
  let (s : {s : Finset I // s.Nonempty}) : Algebra.FinitePresentation S (M.obj s) := inferInstance
  have parameters := @chosen_parameters.{u} K kField kClosed kZero G i I iFinite
    S hS M (inferInstanceAs (∀ s, Algebra.FinitePresentation S (M.obj s)))
    (inferInstanceAs (∀ s, Algebra.Smooth S (M.obj s))) F e he sel beta hnatural hbeta
  obtain ⟨R, hSR, hR, heR, H⟩ := parameters
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let N := fixedFibreDiagram (R := R) (M := R) M
  let eR := @scalarDiagramComparison.{u,u,u} K kField S R hSR
        {s : Finset I // s.Nonempty}
        (inferInstanceAs (Category.{u} {s : Finset I // s.Nonempty})) M F e
  let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let YR := pullback base sr
  let baseR := pullback.snd base sr
  let qR := pullback.fst base sr
  let B := intersectionOpens U
  let V : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ YR.Opens :=
    { obj := fun s ↦ qR ⁻¹ᵁ B.obj s
      map := fun f ↦ homOfLE (qR.preimage_mono (leOfHom (B.map f))) }
  let E := V ⋙ YR.restrictFunctor ⋙ Over.map baseR
  let C := (E ⋙ algΓ (.of R)).unop
  let : YR.IsSeparated := ⟨by rw [← terminal.comp_from baseR]; infer_instance⟩
  obtain ⟨hE, d, cG, hpure, hpt, ⟨hcG⟩, hleg⟩ :=
    exists_fixed_coordinate_projection (R := R) base U hU hcover
  have hproper : IsProper cG.pt.hom := by
    rw [hpt]
    change IsProper baseR
    infer_instance
  let UR := fun j ↦ qR ⁻¹ᵁ U j
  have hUR (j : I) : IsAffineOpen (UR j) := by
    have : IsAffine (U j).toScheme := hU j
    exact IsAffine.of_isPullback
      ((isPullback_morphismRestrict qR (U j)).paste_vert (IsPullback.of_hasPullback base sr))
  have hV : V = intersectionOpens UR :=
    CategoryTheory.Functor.ext (fun s ↦ by
      change qR ⁻¹ᵁ (⨅ j ∈ s.unop.val, U j) = ⨅ j ∈ s.unop.val, qR ⁻¹ᵁ U j
      rw [← Finset.inf_eq_iInf, ← Finset.inf_eq_iInf]
      exact map_finset_inf qR.base.frameHom _ _) (fun _ _ _ ↦ Subsingleton.elim _ _)
  have hC : C = intersectionCoordinates baseR (intersectionOpens UR) :=
    congrArg (fun W : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ YR.Opens ↦
      ((W ⋙ YR.restrictFunctor ⋙ Over.map baseR) ⋙ algΓ (.of R)).unop) hV
  let dStd : N ≅ intersectionCoordinates baseR (intersectionOpens UR) := d ≪≫ eqToIso hC
  have hopen := coordinate_diagram_opens baseR UR hUR N dStd
  let {s t} (f : s ⟶ t) : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom)) := hopen.1 s t f
  let : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected := hopen.2
  refine ⟨R, hSR, ?_⟩
  refine ⟨hR, heR, ?_⟩
  refine ⟨hE, d, cG, hpure, hpt, ⟨hcG⟩, hproper, hleg, ?_⟩
  let scale := fun s j hj k hk ↦ Units.map
    (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
      (simpleRootCoefficient G i)
  let shift := fun s j hj k hk ↦ simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
    ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)
  exact bundle_of_parameters (I := I) (R := R) (K := K) N F eR sel scale shift cG hcG H

end SchubertGeometry
