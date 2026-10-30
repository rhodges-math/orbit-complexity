import OrbitComplexity.FrobeniusSplitting.Normality.Models.FixedDiagramIsos
import OrbitComplexity.FrobeniusSplitting.Normality.Products.PointedFamilyHelpers
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.JointOpenModels
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.IntersectionModelCover
import OrbitComplexity.FrobeniusSplitting.Normality.Smooth

/-! # The specified coordinate diagram gives the global smooth model -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace FrobeniusSplitting
noncomputable section
universe u v w

/-- The two retained diagram isomorphisms compose on the extension of
the original diagram, rather than on a newly chosen coordinate diagram. -/
private def twoStageDiagramIso {J : Type v} [Category.{w} J]
    {S T R : Type u} [CommRing S] [CommRing T] [CommRing R]
    [Algebra S T] [Algebra T R] [Algebra S R] [IsScalarTower S T R]
    {P : J ⥤ CommAlgCat.{u} S} {Q : J ⥤ CommAlgCat.{u} T}
    {N : J ⥤ CommAlgCat.{u} R}
    (a : fixedFibreDiagram (R := T) (M := T) P ≅ Q)
    (b : fixedFibreDiagram (R := R) (M := R) Q ≅ N) :
    fixedFibreDiagram (R := R) (M := R) P ≅ N :=
  (fixedFibreCancelIso P).symm ≪≫ fixedFibreDiagramIso a ≪≫ b

private theorem tensor_comparison_pure
    {S T R K M Q N A : Type u}
    [CommRing S] [CommRing T] [CommRing R] [CommRing K]
    [CommRing M] [CommRing Q] [CommRing N] [CommRing A]
    [Algebra S T] [Algebra T R]
    [Algebra R K] [Algebra T K] [Algebra S K]
    [IsScalarTower S T K] [IsScalarTower T R K]
    [Algebra S M] [Algebra T Q] [Algebra R N] [Algebra K A]
    [Algebra R A] [Algebra T A]
    [IsScalarTower R K A] [IsScalarTower T K A]
    (e : K ⊗[S] M ≃ₐ[K] A) (eT : K ⊗[T] Q ≃ₐ[K] A)
    (eR : K ⊗[R] N ≃ₐ[K] A)
    (a : T ⊗[S] M →ₐ[T] Q) (b : R ⊗[T] Q →ₐ[R] N)
    (ha : ∀ x, eT ((1 : K) ⊗ₜ[T] a x) = scalarImageHom (R := T) e x)
    (hb : ∀ x, eR ((1 : K) ⊗ₜ[R] b x) = scalarImageHom (R := R) eT x)
    (r : R) (x : M) :
    eR ((1 : K) ⊗ₜ[R] b (r ⊗ₜ[T] a ((1 : T) ⊗ₜ[S] x))) =
      e (algebraMap R K r ⊗ₜ[S] x) := by
  rw [hb]
  have h := ha ((1 : T) ⊗ₜ[S] x)
  simp only [scalarImageHom, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    Algebra.ofId_apply, AlgHom.id_apply, map_one] at h ⊢
  calc
    eT (algebraMap R K r ⊗ₜ[T] a ((1 : T) ⊗ₜ[S] x)) =
        algebraMap R K r • eT ((1 : K) ⊗ₜ[T] a ((1 : T) ⊗ₜ[S] x)) := by
      rw [← map_smul]
      congr 1
      simp [Algebra.smul_def]
    _ = algebraMap R K r • e ((1 : K) ⊗ₜ[S] x) := congrArg _ h
    _ = e (algebraMap R K r ⊗ₜ[S] x) := by
      rw [← map_smul]
      congr 1
      simp [Algebra.smul_def]

/-- Both retained component evaluations imply the original comparison after
the cancellation of the successive coefficient extensions. -/
private theorem twoStageDiagramIso_evaluation {J : Type v} [Category.{w} J]
    {S T R K : Type u} [CommRing S] [CommRing T] [CommRing R] [CommRing K]
    [Algebra S T] [Algebra T R] [Algebra S R] [IsScalarTower S T R]
    [Algebra R K] [Algebra T K] [Algebra S K]
    [IsScalarTower S T K] [IsScalarTower T R K] [IsScalarTower S R K]
    {P : J ⥤ CommAlgCat.{u} S} {Q : J ⥤ CommAlgCat.{u} T}
    {N : J ⥤ CommAlgCat.{u} R} {F : J ⥤ CommAlgCat.{u} K}
    [∀ i, Algebra R (F.obj i)] [∀ i, Algebra T (F.obj i)]
    [∀ i, IsScalarTower R K (F.obj i)] [∀ i, IsScalarTower T K (F.obj i)]
    (e : ∀ i, K ⊗[S] P.obj i ≃ₐ[K] F.obj i)
    (eT : ∀ i, K ⊗[T] Q.obj i ≃ₐ[K] F.obj i)
    (eR : ∀ i, K ⊗[R] N.obj i ≃ₐ[K] F.obj i)
    (a : fixedFibreDiagram (R := T) (M := T) P ≅ Q)
    (b : fixedFibreDiagram (R := R) (M := R) Q ≅ N)
    (ha : ∀ i x, eT i ((1 : K) ⊗ₜ[T] (a.hom.app i).hom x) =
      scalarImageHom (R := T) (e i) x)
    (hb : ∀ i x, eR i ((1 : K) ⊗ₜ[R] (b.hom.app i).hom x) =
      scalarImageHom (R := R) (eT i) x) (i : J)
    (z : R ⊗[S] P.obj i) :
    eR i ((1 : K) ⊗ₜ[R] ((twoStageDiagramIso a b).hom.app i).hom z) =
      ((Algebra.TensorProduct.cancelBaseChange S R K K (P.obj i)).trans (e i))
        ((1 : K) ⊗ₜ[R] z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
      have hstep : ((twoStageDiagramIso a b).hom.app i).hom (r ⊗ₜ[S] x) =
          (b.hom.app i).hom (r ⊗ₜ[T] (a.hom.app i).hom ((1 : T) ⊗ₜ[S] x)) := by
        change (b.hom.app i).hom
            ((Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
              (CommAlgCat.algEquivOfIso (a.app i)))
              ((Algebra.TensorProduct.cancelBaseChange S T R R (P.obj i)).symm
                (r ⊗ₜ[S] x))) = _
        rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
        rfl
      rw [hstep, AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_tmul]
      simpa only [Algebra.smul_def, mul_one] using
        tensor_comparison_pure (e i) (eT i) (eR i)
          (a.hom.app i).hom (b.hom.app i).hom (ha i) (hb i) r x
  | add x y hx hy =>
      simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hx hy


/-- Component evaluation commutes with the transported cocone leg itself. -/
private theorem transported_model_leg {J : Type v} [Category.{w} J]
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {P N : J ⥤ CommAlgCat.{u} R} (F : J ⥤ CommAlgCat.{u} K)
    (a : P ≅ N) (c : Cocone (N.op ⋙ algSpec (.of R)))
    (eP : ∀ i, K ⊗[R] P.obj i ≃ₐ[K] F.obj i)
    (eN : ∀ i, K ⊗[R] N.obj i ≃ₐ[K] F.obj i)
    (hP : ∀ i j (f : i ⟶ j), (eP j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (P.map f).hom) =
      (F.map f).hom.comp (eP i).toAlgHom)
    (hN : ∀ i j (f : i ⟶ j), (eN j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
      (F.map f).hom.comp (eN i).toAlgHom)
    (he : ∀ i z, eN i ((1 : K) ⊗ₜ[R] (a.hom.app i).hom z) =
      eP i ((1 : K) ⊗ₜ[R] z)) (s : Jᵒᵖ) :
    (affineModelNatTrans P F eP hP).app s ≫
        ((transportModelCocone a c).ι.app s).left =
      (affineModelNatTrans N F eN hN).app s ≫ (c.ι.app s).left := by
  have hring : ((eP s.unop).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom).comp
        (a.inv.app s.unop).hom.toRingHom =
      (eN s.unop).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    have h := he s.unop ((a.inv.app s.unop).hom x)
    simpa using h.symm
  let fP := Spec.map (CommRingCat.ofHom
    ((eP s.unop).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))
  let u := Spec.map (CommRingCat.ofHom (a.inv.app s.unop).hom.toRingHom)
  let fN := Spec.map (CommRingCat.ofHom
    ((eN s.unop).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))
  let leg : Spec (.of (N.obj s.unop)) ⟶ c.pt.left := (c.ι.app s).left
  have hspec : fP ≫ u = fN := by
    dsimp only [fP, u, fN]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
  have hpost : (fP ≫ u) ≫ leg = fN ≫ leg :=
    congrArg (fun f => f ≫ leg) hspec
  change fP ≫ (u ≫ leg) = fN ≫ leg
  exact (Category.assoc fP u leg).symm.trans hpost


private def intersectionPayload {X : Scheme.{u}} {I K S R : Type u}
    [CommRing K] [CommRing S] [CommRing R]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (base : X ⟶ Spec (.of K)) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (P : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (e : ∀ s, K ⊗[S] P.obj s ≃ₐ[K] (intersectionCoordinates base (intersectionOpens U)).obj s)
    (fg : Prop) : Prop :=
  let N := fixedFibreDiagram (R := R) (M := R) P
  let eR (i) := (Algebra.TensorProduct.cancelBaseChange S R K K (P.obj i)).trans (e i)
  ∃ (heR : ∀ s t (f : s ⟶ t), (eR t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
    ((intersectionCoordinates base (intersectionOpens U)).map f).hom.comp (eR s).toAlgHom)
    (c : Cocone (N.op ⋙ algSpec (.of R))) (q : X ⟶ c.pt.left),
    fg ∧ Nonempty (IsColimit c) ∧
    IsPullback q base c.pt.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
    (∀ s, ((intersectionCoordinateCocone base U hU).ι.app s).left ≫ q =
      (affineModelNatTrans N (intersectionCoordinates base (intersectionOpens U)) eR heR).app s ≫
        (c.ι.app s).left) ∧
    CompactSpace c.pt.left ∧ LocallyOfFinitePresentation c.pt.hom ∧ Smooth c.pt.hom ∧
    (∀ s, IsOpenImmersion (c.ι.app s).left) ∧
    (∀ y : c.pt.left, ∃ s x, (c.ι.app s).left x = y) ∧
    (∀ (T : Scheme.{u}) (f : T ⟶ c.pt.left) (y : T),
      ∃ s, ∃ z : (pullback f (c.ι.app s).left : Scheme.{u}),
        (pullback.fst f (c.ι.app s).left) z = y) ∧
    ∀ (L : Type u) (_ : Field L) (f : R →+* L)
      (z : (pullback (Spec.map (CommRingCat.ofHom f)) c.pt.hom : Scheme.{u})),
      IsDomain ((pullback (Spec.map (CommRingCat.ofHom f)) c.pt.hom :
        Scheme.{u}).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback (Spec.map (CommRingCat.ofHom f)) c.pt.hom :
        Scheme.{u}).presheaf.stalk z)

private theorem intersection_payload_of_refinement
    {X : Scheme.{u}} {I K S R : Type u}
    [CommRing K] [CommRing S] [CommRing R]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (base : X ⟶ Spec (.of K)) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (P : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (e : ∀ s, K ⊗[S] P.obj s ≃ₐ[K] (intersectionCoordinates base (intersectionOpens U)).obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (P.map f).hom) =
      ((intersectionCoordinates base (intersectionOpens U)).map f).hom.comp (e s).toAlgHom)
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (eN : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] (intersectionCoordinates base (intersectionOpens U)).obj s)
    (heN : ∀ s t (f : s ⟶ t), (eN t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
      ((intersectionCoordinates base (intersectionOpens U)).map f).hom.comp (eN s).toAlgHom)
    (phi : fixedFibreDiagram (R := R) (M := R) P ≅ N)
    (hphi : ∀ s x, eN s ((1 : K) ⊗ₜ[R] (phi.hom.app s).hom x) =
      ((Algebra.TensorProduct.cancelBaseChange S R K K (P.obj s)).trans (e s))
        ((1 : K) ⊗ₜ[R] x))
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (q : X ⟶ cN.pt.left)
    {fg : Prop} (hfg : fg) (hcN : Nonempty (IsColimit cN))
    (hcart : IsPullback q base cN.pt.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hleg : ∀ s, ((intersectionCoordinateCocone base U hU).ι.app s).left ≫ q =
      (affineModelNatTrans N (intersectionCoordinates base (intersectionOpens U)) eN heN).app s ≫
        (cN.ι.app s).left)
    (hcompact : CompactSpace cN.pt.left) (hlfp : LocallyOfFinitePresentation cN.pt.hom)
    (hsmooth : Smooth cN.pt.hom) (hopenN : ∀ s, IsOpenImmersion (cN.ι.app s).left)
    (hcovN : ∀ y : cN.pt.left, ∃ s x, (cN.ι.app s).left x = y)
    (hbc : ∀ (T : Scheme.{u}) (f : T ⟶ cN.pt.left) (y : T),
      ∃ s, ∃ z : (pullback f (cN.ι.app s).left : Scheme.{u}),
        (pullback.fst f (cN.ι.app s).left) z = y) :
    intersectionPayload (R := R) base U hU P e fg := by
  let F := intersectionCoordinates base (intersectionOpens U)
  let eR (s) := (Algebra.TensorProduct.cancelBaseChange S R K K (P.obj s)).trans (e s)
  have heR := extendedComparison_natural P F e he (R := R)
  let c := transportModelCocone phi cN
  have hcp := transportModelCocone_properties phi cN hcN.some hopenN hbc
  refine ⟨heR, c, q, hfg, hcp.1, hcart, ?_,
    hcompact, hlfp, hsmooth, hcp.2.1, ?_, hcp.2.2, ?_⟩
  · intro s
    exact (hleg s).trans (transported_model_leg F phi cN eR eN heR heN hphi s).symm
  · intro y
    obtain ⟨s, z, hz⟩ := hcovN y
    let delta := Functor.isoWhiskerRight (NatIso.op phi.symm) (algSpec (.of R))
    let a := (Over.forget (Spec (.of R))).mapIso (delta.app s)
    refine ⟨s, a.inv z, ?_⟩
    change (a.inv ≫ a.hom ≫ (cN.ι.app s).left) z = y
    have hcancel : a.inv ≫ a.hom ≫ (cN.ι.app s).left = (cN.ι.app s).left := by simp
    exact (congrArg (fun f => f z) hcancel).trans hz
  · intro L _ f z
    let : Smooth c.pt.hom := hsmooth
    exact stalks_of_smooth (pullback.fst
      (Spec.map (CommRingCat.ofHom f)) c.pt.hom) z

/-- Open-model retention and gluing preserve the original nodes, all arrows,
the original generic comparison and every chart leg. -/
theorem exists_intersection_model {X : Scheme.{u}} {I K : Type u}
    [Finite I] [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (base : X ⟶ Spec (.of K)) (U : I → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (S : Subalgebra ℤ K) (hS : S.FG)
    (P : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [∀ s, Algebra.FinitePresentation S (P.obj s)]
    [∀ s, Algebra.Smooth S (P.obj s)]
    (e : ∀ s, K ⊗[S] P.obj s ≃ₐ[K] (intersectionCoordinates base (intersectionOpens U)).obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (P.map f).hom) =
      ((intersectionCoordinates base (intersectionOpens U)).map f).hom.comp (e s).toAlgHom)
    (hopen : ∀ s t (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((intersectionCoordinates base (intersectionOpens U)).map
        f).hom.toRingHom))) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      intersectionPayload (R := R) base U hU P e R.FG := by
  classical
  let C := {s : Finset I // s.Nonempty}
  let F := intersectionCoordinates base (intersectionOpens U)
  have H := exists_joint_open_models S hS P F e he hopen
    (fun _ => Empty) (fun _ x => x.elim)
  rcases H with ⟨L, hL, a, hcoverL, hlocal, T, hST, hdata⟩
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  rcases hdata with ⟨Q, eT, d, hd, hT, hfp, hsm, heval, hvalues, hrange,
    hdenom, hretained⟩
  let QD := modelFunctor (fun i => Q i) (F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    d (fun i => (Q i).val.toRingHom) (fun _ => Subtype.val_injective) hd
  rcases hretained with ⟨⟨aT, haT⟩, R, hTR, hfinal⟩
  let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  let : IsScalarTower T R K := Subalgebra.inclusion.isScalarTower_right hTR K
  let : Algebra S R := (Subalgebra.inclusion (hST.trans hTR)).toAlgebra
  let : IsScalarTower S R K :=
    Subalgebra.inclusion.isScalarTower_right (hST.trans hTR) K
  let : IsScalarTower S T R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rcases hfinal with ⟨N, eN, hR, hNfp, hNsm, heN, hinj, hNopen, hpush, bR, hbR⟩
  let (s : C) : Algebra.FinitePresentation R (N.obj s) := hNfp s
  let (s : C) : Algebra.Smooth R (N.obj s) := hNsm s
  let P_R := fixedFibreDiagram (R := R) (M := R) P
  let eR (s : C) := (Algebra.TensorProduct.cancelBaseChange S R K K (P.obj s)).trans (e s)
  let phi : P_R ≅ N := twoStageDiagramIso aT bR
  have haT' (s : C) (x) : eT s ((1 : K) ⊗ₜ[T] (aT.hom.app s).hom x) =
      scalarImageHom (R := T) (e s) x := by
    rw [heval]
    exact haT s x
  have hphi (s : C) (x) : eN s ((1 : K) ⊗ₜ[R] (phi.hom.app s).hom x) =
      eR s ((1 : K) ⊗ₜ[R] x) :=
    twoStageDiagramIso_evaluation e eT eN aT bR haT' hbR s x
  obtain ⟨cN, q, hcN, hcart, hleg, hcompact, hlfp, hsmooth, hopenN, hcovN, hbc⟩ :=
    intersection_model_cover base U hU hcover N eN heN hNopen hpush
  refine ⟨R, hST.trans hTR, ?_⟩
  exact intersection_payload_of_refinement base U hU P e he N eN heN phi hphi cN q
    hR hcN hcart hleg hcompact hlfp hsmooth hopenN hcovN hbc

end
end FrobeniusSplitting
