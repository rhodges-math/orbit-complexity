import OrbitComplexity.SchubertGeometry.Normality.Bundles.ChosenProperBundle
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.PriorOpenCoordinateLeg
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.PreimageCoordinateCocone
import Batteries.Tactic.Lint

/-! # comparison of the specified proper prior coordinate cocone -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
noncomputable section
universe u v w
open FrobeniusSplitting

namespace SchubertGeometry

namespace RetainedCharacter

private def inverseOpenDiagram {Y X : Scheme.{u}} (q : X ⟶ Y)
    {J : Type v} [jCat : Category.{w} J] (B : Jᵒᵖ ⥤ Y.Opens) : Jᵒᵖ ⥤ X.Opens where
  obj s := q ⁻¹ᵁ B.obj s
  map f := homOfLE (q.preimage_mono (leOfHom (B.map f)))

private def fieldSchemeDiagram {K : Type u} [kComm : CommRing K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) {J : Type v} [jCat : Category.{w} J]
    (V : Jᵒᵖ ⥤ X.Opens) : Jᵒᵖ ⥤ Over (Spec (.of K)) :=
  V ⋙ X.restrictFunctor ⋙ Over.map base


end RetainedCharacter

private theorem tensor_ringHom_ext {S R A B : Type u}
    [CommRing S] [CommRing R] [CommRing A] [CommRing B]
    [Algebra S R] [Algebra S A] (f g : R ⊗[S] A →+* B)
    (h : ∀ r x, f (r ⊗ₜ[S] x) = g (r ⊗ₜ[S] x)) : f = g := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r x => exact h r x
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem spec_leg_congr {A B : Type u} [CommRing A] [CommRing B]
    {X Y : Scheme.{u}} {b : Spec (.of B) ⟶ X} {m : X ⟶ Y}
    {l : Spec (.of A) ⟶ Y} {f : A →+* B}
    (h : b ≫ m = Spec.map (CommRingCat.ofHom f) ≫ l)
    {g : A →+* B} (e : f = g) :
    b ≫ m = Spec.map (CommRingCat.ofHom g) ≫ l := by
  cases e
  exact h

private theorem projection_over_iso {X Z T : Scheme.{u}}
    (A B : Over T) (e : A ≅ B) (m : X ⟶ B.left) (q : B.left ⟶ Z)
    (r : X ⟶ Z) (h : m ≫ q = r) :
    (m ≫ e.inv.left) ≫ e.hom.left ≫ q = r := by
  have he : e.inv.left ≫ e.hom.left = 𝟙 B.left :=
    congrArg (fun f ↦ f.left) e.inv_hom_id
  have hc : (m ≫ e.inv.left) ≫ e.hom.left = m := by
    rw [Category.assoc, he, Category.comp_id]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun f ↦ f ≫ q) hc).trans h)

private theorem coordinate_inverse_left {J : Type v} [Category.{w} J]
    (R : CommRingCat.{u}) (E : J ⥤ Over (Spec R))
    [∀ j, IsAffine (E.obj j).left] (j : J) :
    ((coordinateDiagramIso R E).inv.app j).left = (E.obj j).left.isoSpec.inv := by
  let η := (algΓAlgSpecAdjunction R).unit.app (E.obj j)
  have : IsIso η := coordinates_unit_isIso R (E.obj j)
  let e : E.obj j ≅ (E ⋙ algΓ R ⋙ algSpec R).obj j := asIso η
  have H : (Over.forget (Spec R)).mapIso e = (E.obj j).left.isoSpec := by
    apply Iso.ext
    change ((algΓAlgSpecAdjunction R).unit.app (E.obj j)).left = _
    dsimp [algΓAlgSpecAdjunction, algΓ, algSpec]
    change (E.obj j).left.toSpecΓ ≫
      Spec.map (𝟙 (CommRingCat.of Γ((E.obj j).left, ⊤))) = _
    exact (congrArg (fun z : Spec (.of Γ((E.obj j).left, ⊤)) ⟶
        Spec (.of Γ((E.obj j).left, ⊤)) ↦ (E.obj j).left.toSpecΓ ≫ z)
      (Spec.map_id (.of Γ((E.obj j).left, ⊤)))).trans (Category.comp_id _)
  change e.inv.left = _
  exact congrArg Iso.inv H

private theorem pullback_over_iso {P T S : Scheme.{u}} (A B : Over S) (e : A ≅ B)
    (m : P ⟶ B.left) (b : P ⟶ T) (g : T ⟶ S)
    (H : IsPullback m b B.hom g) :
    IsPullback (m ≫ e.inv.left) b A.hom g := by
  let eS := (Over.forget S).mapIso e
  exact H.of_iso (Iso.refl P) eS.symm (Iso.refl T) (Iso.refl S)
    (by simp [eS]) (by simp) (by
      change B.hom ≫ 𝟙 S = e.inv.left ≫ A.hom
      exact (Category.comp_id _).trans e.inv.w.symm) (by simp)

private theorem leg_over_iso {P X : Scheme.{u}} {S : Scheme.{u}}
    (A B : Over S) (e : A ≅ B) (a : P ⟶ X) (m : X ⟶ B.left)
    (f : P ⟶ A.left) (h : a ≫ m = f ≫ e.hom.left) :
    a ≫ (m ≫ e.inv.left) = f := by
  calc
    _ = (a ≫ m) ≫ e.inv.left := (Category.assoc _ _ _).symm
    _ = (f ≫ e.hom.left) ≫ e.inv.left := congrArg (fun z ↦ z ≫ e.inv.left) h
    _ = f := by
      have H : e.hom.left ≫ e.inv.left = 𝟙 A.left :=
        congrArg (fun z ↦ z.left) e.hom_inv_id
      rw [Category.assoc, H, Category.comp_id]

/-- The specified coordinate cocone of the prior pullback has the original
scheme as its scalar fibre, with every original coordinate leg. -/
theorem prior_coordinate_cocone_comparison {S R K : Type u}
    [sComm : CommRing S] [rComm : CommRing R] [kComm : CommRing K]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    {Y YK : Scheme.{u}} (base : Y ⟶ Spec (.of S)) [IsProper base]
    (baseK : YK ⟶ Spec (.of K)) (qK : YK ⟶ Y)
    (hK : IsPullback qK baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    {J : Type v} [jCat : Category.{w} J] (B : Jᵒᵖ ⥤ Y.Opens)
    (hB : ∀ s, IsAffineOpen (B.obj s)) :
    let M := @FrobeniusSplitting.intersectionCoordinates.{u,v,w} S sComm Y base J jCat B
    let N := fixedFibreDiagram (R := R) (M := R) M
    let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
    let YR := pullback base sr
    let qR := pullback.fst base sr
    let baseR := pullback.snd base sr
    let VR := @RetainedCharacter.inverseOpenDiagram.{u,v,w} Y YR qR J jCat B
    let VK := @RetainedCharacter.inverseOpenDiagram.{u,v,w} Y YK qK J jCat B
    let ER := @RetainedCharacter.fieldSchemeDiagram.{u,v,w} R rComm YR baseR J jCat VR
    let EK := @RetainedCharacter.fieldSchemeDiagram.{u,v,w} K kComm YK baseK J jCat VK
    let CR := @FrobeniusSplitting.intersectionCoordinates.{u,v,w} R rComm YR baseR J jCat VR
    let FK := @FrobeniusSplitting.intersectionCoordinates.{u,v,w} K kComm YK baseK J jCat VK
    let vR : ∀ s, M.obj s →+* CR.obj s :=
      fun s ↦ (qR ∣_ B.obj (.op s)).appTop.hom
    let vK : ∀ s, M.obj s →+* FK.obj s :=
      fun s ↦ (qK ∣_ B.obj (.op s)).appTop.hom
    ∀ (hER : ∀ s, IsAffine (ER.obj s).left)
      (hEK : ∀ s, IsAffine (EK.obj s).left),
    letI := hER
    letI := hEK
    ∀ (d : N ≅ CR) (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] FK.obj s)
      (eR : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] FK.obj s)
      (cG : Cocone (N.op ⋙ algSpec (.of R))) (hpt : cG.pt = Over.mk baseR)
      (b : (FK.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
        (Functor.const _).obj YK),
      (∀ s r x, (d.hom.app s).hom (r ⊗ₜ[S] x) =
        algebraMap R (CR.obj s) r * vR s x) →
      (∀ s k x, e s (k ⊗ₜ[S] x) =
        algebraMap K (FK.obj s) k * vK s x) →
      (∀ s k r x, eR s (k ⊗ₜ[R] (r ⊗ₜ[S] x)) =
        e s ((algebraMap R K r * k) ⊗ₜ[S] x)) →
      (∀ s, (cG.ι.app s ≫ eqToHom hpt).left =
        Spec.map (CommRingCat.ofHom (d.inv.app s.unop).hom.toRingHom) ≫
          ((coordinateDiagramIso (.of R) ER).inv.app s).left ≫ (VR.obj s).ι) →
      (∀ s, b.app s =
        ((coordinateDiagramIso (.of K) EK).inv.app s).left ≫ (VK.obj s).ι) →
      ∃ m₀ : YK ⟶ cG.pt.left,
        IsPullback m₀ baseK cG.pt.hom
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
        m₀ ≫ (eqToHom hpt).left ≫ qR = qK ∧
        ∀ s, b.app (.op s) ≫ m₀ =
          Spec.map (CommRingCat.ofHom
            ((eR s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
                (cG.ι.app (.op s)).left := by
  intro M N sr YR qR baseR VR VK ER EK CR FK vR vK hER hEK
  let := hER
  let := hEK
  intro d e eR cG hpt b hd he heR hmodel hnative
  obtain ⟨m, _, Hm, hmq, hmb, _⟩ :=
    exists_prior_scalar_extension (S := S) (R := R) (K := K) base baseK qK hK
  have Hlegs (s : J) :
      b.app (.op s) ≫ m =
        Spec.map (CommRingCat.ofHom
          (((Algebra.TensorProduct.cancelBaseChange S R K K (M.obj s)).trans
            (e s)).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
              (cG.ι.app (.op s) ≫ eqToHom hpt).left := by
    let : IsAffine (VK.obj (.op s)).toScheme := hEK (.op s)
    let : IsAffine (VR.obj (.op s)).toScheme := hER (.op s)
    let ds := CommAlgCat.algEquivOfIso (d.app s)
    have H := prior_open_coordinate_leg (S := S) (R := R) (K := K)
      base baseK qK hK (B.obj (.op s)) (hB (.op s)) m hmq hmb ds (e s)
      (hd s) (he s)
    have hnative' : b.app (.op s) =
        (VK.obj (.op s)).toScheme.isoSpec.inv ≫ (VK.obj (.op s)).ι :=
      (hnative (.op s)).trans
        (congrArg (fun z ↦ z ≫ (VK.obj (.op s)).ι)
          (coordinate_inverse_left (.of K) EK (.op s)))
    have hmodel' : (cG.ι.app (.op s) ≫ eqToHom hpt).left =
        Spec.map (CommRingCat.ofHom ds.symm.toRingHom) ≫
          (VR.obj (.op s)).toScheme.isoSpec.inv ≫ (VR.obj (.op s)).ι :=
      (hmodel (.op s)).trans
        (congrArg (fun z ↦ Spec.map (CommRingCat.ofHom ds.symm.toRingHom) ≫
            z ≫ (VR.obj (.op s)).ι)
          (coordinate_inverse_left (.of R) ER (.op s)))
    calc
      _ = ((VK.obj (.op s)).toScheme.isoSpec.inv ≫ (VK.obj (.op s)).ι) ≫ m :=
        congrArg (fun z ↦ z ≫ m) hnative'
      _ = _ := by
        rw [Category.assoc]
        exact H.trans (congrArg (fun z ↦ _ ≫ z) hmodel'.symm)
  have hmaps (s : J) :
      ((Algebra.TensorProduct.cancelBaseChange S R K K (M.obj s)).trans
        (e s)).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      (eR s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom := by
    apply tensor_ringHom_ext
    intro r x
    change e s (Algebra.TensorProduct.cancelBaseChange S R K K (M.obj s)
      ((1 : K) ⊗ₜ[R] (r ⊗ₜ[S] x))) = eR s ((1 : K) ⊗ₜ[R] (r ⊗ₜ[S] x))
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    simpa only [Algebra.smul_def] using (heR s 1 r x).symm
  let ept : cG.pt ≅ Over.mk baseR := eqToIso hpt
  let m₀ : YK ⟶ cG.pt.left := m ≫ ept.inv.left
  refine ⟨m₀, pullback_over_iso cG.pt (Over.mk baseR) ept m baseK
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) Hm,
    projection_over_iso cG.pt (Over.mk baseR) ept m qR qK hmq, fun s ↦ ?_⟩
  have hLeg := leg_over_iso cG.pt (Over.mk baseR) ept (b.app (.op s)) m
    (Spec.map (CommRingCat.ofHom
      (((Algebra.TensorProduct.cancelBaseChange S R K K (M.obj s)).trans
        (e s)).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          (cG.ι.app (.op s)).left) ((Hlegs s).trans (Category.assoc _ _ _).symm)
  exact spec_leg_congr hLeg (hmaps s)


end SchubertGeometry
