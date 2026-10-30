import OrbitComplexity.SchubertGeometry.Normality.Bundles.PriorBundleProjection
import OrbitComplexity.SchubertGeometry.Normality.BottSamelson.BorelAppendModel
import OrbitComplexity.SchubertGeometry.Normality.Transitions.ProperEndpointCharts
import OrbitComplexity.SchubertGeometry.Normality.Transitions.TransitionFamilies
import OrbitComplexity.SchubertGeometry.Normality.Bundles.BundleInfinityComparison
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # An append model over the same proper prior model -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u
namespace SchubertGeometry

open private RetainedCharacter.inverseOpenDiagram RetainedCharacter.fieldSchemeDiagram
  from OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison

private theorem point_pullback {S T Y : Scheme.{u}} (f : Y ⟶ S) (g : T ⟶ S)
    (P : Over T) (e : P ≅ Over.mk (pullback.snd f g)) :
    IsPullback (e.hom.left ≫ pullback.fst f g) P.hom f g := by
  let eS := (Over.forget T).mapIso e
  exact (IsPullback.of_hasPullback f g).of_iso' eS (Iso.refl Y)
    (Iso.refl T) (Iso.refl S) (by simp [eS])
    (by exact e.hom.w.trans (Category.comp_id _).symm) (by simp) (by simp)

private theorem opens_from_preimage_coordinates {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} [X.IsSeparated] (base : X ⟶ Spec (.of R)) (q : X ⟶ Y)
    {I : Type u} (U : I → Y.Opens)
    (hU : ∀ j, IsAffineOpen (q ⁻¹ᵁ U j))
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (d : N ≅ intersectionCoordinates base (RetainedCharacter.inverseOpenDiagram q (intersectionOpens
      U))) :
    (∀ s t (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))) ∧
    ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected := by
  have hV : RetainedCharacter.inverseOpenDiagram q (intersectionOpens U) = intersectionOpens (fun j
    ↦ q ⁻¹ᵁ U j) :=
    CategoryTheory.Functor.ext (fun s ↦ by
      change q ⁻¹ᵁ (⨅ j ∈ s.unop.val, U j) = ⨅ j ∈ s.unop.val, q ⁻¹ᵁ U j
      rw [← Finset.inf_eq_iInf, ← Finset.inf_eq_iInf]
      exact map_finset_inf q.base.frameHom _ _) (fun _ _ _ ↦ Subsingleton.elim _ _)
  have hC : intersectionCoordinates base (RetainedCharacter.inverseOpenDiagram q (intersectionOpens
    U)) =
      intersectionCoordinates base (intersectionOpens (fun j ↦ q ⁻¹ᵁ U j)) :=
    congrArg (intersectionCoordinates base) hV
  exact coordinate_diagram_opens base (fun j ↦ q ⁻¹ᵁ U j) hU N (d ≪≫ eqToIso hC)

private theorem append_from_fixed_models {K R : Type u} [kField : Field K]
    [kClosed : IsAlgClosed K] [kZero : CharZero K] [rComm : CommRing R]
    [rKAlg : Algebra R K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (U : (bsdhScheme G word).OpenCover.{u})
    (F : {s : Finset U.I₀ // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (N : {s : Finset U.I₀ // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
        (F.map f).hom.comp (e s).toAlgHom)
    [fOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [fDir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    [nOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [nDir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (p : ∀ (s : {s : Finset U.I₀ // s.Nonempty}) (j : U.I₀) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (.op (F.obj s)) ⟶ Over.mk (U.f j ≫ bsdhToSpec G word))
    (g : U.I₀ → G.points)
    (a : ∀ j, Over.mk (U.f j ≫ bsdhToSpec G word) ⟶
      (oppositeUnipotentVariety G).toOver)
    (c : ∀ j, Over.mk (U.f j ≫ bsdhToSpec G word) ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (ha : ∀ j, (a j).left ≫ flagSchemeChart G (g j) = U.f j ≫ bsdhMap G word)
    (hend : ∀ j, (c j).left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a j ⊗ₘ 𝟙 _).left ≫ flagBundleChart G _ (g j))
    (hpn : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val),
      (algSpec (.of K)).map (F.map f).op ≫ p s j hj = p t j ((leOfHom f) hj))
    (beta : ∀ (s : {s : Finset U.I₀ // s.Nonempty}) (j : U.I₀) (_ : j ∈ s.val)
      (k : U.I₀) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hchart : ∀ s j hj k hk,
      (p s j hj ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) ≫ c j =
      (overlapTwist (Y := (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver) (beta s j hj k hk)).hom ≫
        (p s k hk ⊗ₘ 𝟙 _) ≫ c k)
    (hnatural : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk)
    (sel : ∀ s : {s : Finset U.I₀ // s.Nonempty}, {j // j ∈ s.val})
    (b : (F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⟶
      (Functor.const _).obj (bsdhScheme G word))
    (hb : IsColimit (Cocone.mk (bsdhScheme G word) b))
    (hpleg : ∀ s j hj, (p s j hj).left ≫ U.f j = b.app (.op s))
    (hbbase : ∀ s, b.app (.op s) ≫ bsdhToSpec G word =
      Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))))
    (hcart : ∀ s, IsPullback
      (fst ((algSpec (.of K)).obj (.op (F.obj s)))
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
      ((p s (sel s).val (sel s).property ⊗ₘ 𝟙 _) ≫ c (sel s).val).left
      (b.app (.op s)) (bsdhAppendFst G word i))
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG)
    [IsProper cG.pt.hom] [Smooth cG.pt.hom]
    (m₀ : bsdhScheme G word ⟶ cG.pt.left)
    (hm₀ : IsPullback m₀ (bsdhToSpec G word) cG.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hbmodel : ∀ s, b.app (.op s) ≫ m₀ =
      Spec.map (CommRingCat.ofHom
        ((e s).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          (cG.ι.app (.op s)).left)
    (hBundle : modelBundleSpec N F e sel
      (fun s j hj k hk ↦ Units.map
        (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
          (simpleRootCoefficient G i))
      (fun s j hj k hk ↦
        simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
          ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G))
      cG) :
    ∃ (Z : Scheme.{u}) (baseZ : Z ⟶ Spec (.of R)) (q : Z ⟶ cG.pt.left)
      (m : bsdhScheme G (word ++ [i]) ⟶ Z),
      baseZ = q ≫ cG.pt.hom ∧ IsProper baseZ ∧ Smooth baseZ ∧
      IsProper q ∧ Smooth q ∧ GeometricallyConnected q ∧
      IsPullback m (bsdhAppendFst G word i) q m₀ ∧
      IsPullback m (bsdhToSpec G (word ++ [i])) baseZ
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      ∃ (δ : cG.pt.left ⟶ Z) (d : bsdhScheme G word ⟶ bsdhScheme G (word ++ [i])),
        δ ≫ q = 𝟙 _ ∧ IsClosedImmersion δ ∧ δ ≫ baseZ = cG.pt.hom ∧
        IsClosedImmersion d ∧ d ≫ bsdhAppendFst G word i = 𝟙 _ ∧
        d ≫ bsdhMap G (word ++ [i]) = bsdhMap G word ∧ d ≫ m = m₀ ≫ δ := by
  obtain ⟨c₀, a₀, hc₀, ha₀, hco, hn, D, eP, π, hproj, hmap, hπ,
    cD, q, hD, hq, hcartD, hproper, hsmooth, hgc, hopen, hcoverage, m, hm, hmq, hlegs⟩ :=
    @borel_append_comparison.{u} K R kField kClosed kZero rComm rKAlg
      G word i U.I₀ (fun j => Over.mk (U.f j ≫ bsdhToSpec G word))
      F N e he fOpen fDir nOpen nDir p c hpn beta hchart hnatural hbeta
      sel b hb hbbase hcart cG m₀ hm₀ hbmodel hBundle
  let : IsProper q := hproper
  let : Smooth q := hsmooth
  let baseZ := q ≫ cG.pt.hom
  let cTransition {s t : {s : Finset U.I₀ // s.Nonempty}ᵒᵖ} (f : s ⟶ t) :
      (N.obj s.unop)ˣ :=
    c₀ s.unop (sel s.unop).val (sel s.unop).property
      (sel t.unop).val ((leOfHom f.unop) (sel t.unop).property)
  let aTransition {s t : {s : Finset U.I₀ // s.Nonempty}ᵒᵖ} (f : s ⟶ t) :
      N.obj s.unop :=
    a₀ s.unop (sel s.unop).val (sel s.unop).property
      (sel t.unop).val ((leOfHom f.unop) (sel t.unop).property)
  have hmapInfinity {s t : {s : Finset U.I₀ // s.Nonempty}ᵒᵖ} (f : s ⟶ t) :
      D.map f ≫ (eP t.unop).hom = (eP s.unop).hom ≫
        (projectiveLineScalingIso (cTransition f)).hom ≫
        (projectiveLineTranslationIso (aTransition f)).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f.unop).hom.toRingHom :=
    hmap t.unop s.unop f.unop
  obtain ⟨δ, hδq, hδclosed, hδleg⟩ := projective_bundle_infinity
    (J := {s : Finset U.I₀ // s.Nonempty}) (R := R)
    N D π (fun s ↦ eP s.unop) (fun s ↦ hproj s.unop)
    cTransition aTransition hmapInfinity cG hcG cD q hq
  have hδbase : δ ≫ baseZ = cG.pt.hom := by
    change δ ≫ (q ≫ cG.pt.hom) = _
    rw [← Category.assoc, hδq, Category.id_comp]
  obtain ⟨dNative, hdclosed, hdπ, hdτ⟩ := bsdh_omitted_section G word i
  have hδnative : dNative ≫ m = m₀ ≫ δ :=
    @SchubertGeometry.bundle_infinity_comparison.{u} K R kField kClosed kZero rComm rKAlg
      G word i U.I₀ (fun j => Over.mk (U.f j ≫ bsdhToSpec G word))
      (fun j => Over.homMk (U.f j) rfl) F N e sel p g a c ha hend b hb hpleg (fun s => (hcart
        s).w.symm)
      cG D eP cD δ (fun s ↦ hδleg (.op s)) m₀ m hbmodel hlegs dNative hdπ hdτ
  exact ⟨cD.pt, baseZ, q, m, rfl, inferInstance, inferInstance,
    hproper, hsmooth, hgc, hmq, hm, δ, dNative,
    hδq, hδclosed, hδbase, hdclosed, hdπ, hdτ, hδnative⟩

-- The append bundle, infinity section and scalar projection are assembled over the same prior model
-- while retaining every chart comparison and both pullback squares.
set_option maxHeartbeats 400000 in
/-- Specified append charts on inverse images of the prior affine cover
construct a proper smooth append model, preserving the prior scalar projection. -/
theorem exists_proper_append_model {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) (hS : S.FG) {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [baseProper : IsProper base] [baseSmooth : Smooth base]
    (qK : bsdhScheme G word ⟶ Y)
    (hK : IsPullback qK (bsdhToSpec G word) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (W : Y.OpenCover.{u}) [wFinite : Finite W.I₀] (hW : ∀ j, IsAffine (W.X j)) :
    let O := fun j ↦ qK ⁻¹ᵁ (W.f j).opensRange
    let hcover : (⨆ j, O j) = ⊤ :=
      (TopologicalSpace.Opens.map_iSup qK.base (fun j ↦ (W.f j).opensRange)).symm.trans
        ((congrArg (fun V : Y.Opens ↦ qK ⁻¹ᵁ V) W.iSup_opensRange).trans
          (TopologicalSpace.Opens.map_top qK.base))
    let U := (bsdhScheme G word).openCoverOfIsOpenCover O hcover
    ∀ (g : W.I₀ → G.points)
      (a : ∀ j, Over.mk (U.f j ≫ bsdhToSpec G word) ⟶
        (oppositeUnipotentVariety G).toOver)
      (c : ∀ j, Over.mk (U.f j ≫ bsdhToSpec G word) ⊗
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
          Over.mk (bsdhToSpec G (word ++ [i]))),
      (∀ j, (a j).left ≫ flagSchemeChart G (g j) = U.f j ≫ bsdhMap G word) →
      (∀ j, IsPullback
        (fst (Over.mk (U.f j ≫ bsdhToSpec G word))
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
        (c j).left (U.f j) (bsdhAppendFst G word i)) →
      (∀ j, (c j).left ≫ (bsdhAppendIso G word i).hom.left ≫
        pullback.snd (bsdhMap G word) (flagBundleProjection G
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
        (a j ⊗ₘ 𝟙 _).left ≫ flagBundleChart G _ (g j)) →
      ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
        letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
        R.FG ∧ ∃ (Y₀ Z : Scheme.{u}) (base₀ : Y₀ ⟶ Spec (.of R))
          (baseZ : Z ⟶ Spec (.of R)) (q₀ : Y₀ ⟶ Y) (q : Z ⟶ Y₀)
          (m₀ : bsdhScheme G word ⟶ Y₀)
          (m : bsdhScheme G (word ++ [i]) ⟶ Z),
          IsProper base₀ ∧ Smooth base₀ ∧
          IsPullback q₀ base₀ base (Spec.map (CommRingCat.ofHom (algebraMap S R))) ∧
          IsPullback m₀ (bsdhToSpec G word) base₀
            (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
          m₀ ≫ q₀ = qK ∧ baseZ = q ≫ base₀ ∧
          IsProper baseZ ∧ Smooth baseZ ∧
          IsProper q ∧ Smooth q ∧ GeometricallyConnected q ∧
          IsPullback m (bsdhAppendFst G word i) q m₀ ∧
          IsPullback m (bsdhToSpec G (word ++ [i])) baseZ
            (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
          ∃ (δ : Y₀ ⟶ Z) (d : bsdhScheme G word ⟶ bsdhScheme G (word ++ [i])),
            δ ≫ q = 𝟙 _ ∧ IsClosedImmersion δ ∧ δ ≫ baseZ = base₀ ∧
            IsClosedImmersion d ∧ d ≫ bsdhAppendFst G word i = 𝟙 _ ∧
            d ≫ bsdhMap G (word ++ [i]) = bsdhMap G word ∧ d ≫ m = m₀ ≫ δ := by
  classical
  let O := fun j ↦ qK ⁻¹ᵁ (W.f j).opensRange
  let hcover : (⨆ j, O j) = ⊤ :=
    (TopologicalSpace.Opens.map_iSup qK.base (fun j ↦ (W.f j).opensRange)).symm.trans
      ((congrArg (fun V : Y.Opens ↦ qK ⁻¹ᵁ V) W.iSup_opensRange).trans
        (TopologicalSpace.Opens.map_top qK.base))
  let U := (bsdhScheme G word).openCoverOfIsOpenCover O hcover
  dsimp only
  intro g a c ha hcart hend
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from base]; infer_instance⟩
  let : (bsdhScheme G word).IsSeparated := ⟨by
    rw [← terminal.comp_from (bsdhToSpec G word)]
    infer_instance⟩
  let Wu := fun j ↦ (W.f j).opensRange
  have hWu (j : W.I₀) : IsAffineOpen (Wu j) := by
    let : IsAffine (W.X j) := hW j
    exact isAffineOpen_opensRange (W.f j)
  have hO (j : W.I₀) : IsAffineOpen (O j) := by
    let : IsAffine (Wu j).toScheme := hWu j
    exact IsAffine.of_isPullback
      ((isPullback_morphismRestrict qK (Wu j)).paste_vert hK)
  let B := intersectionOpens Wu
  let V := @RetainedCharacter.inverseOpenDiagram.{u,u,u} Y (bsdhScheme G word) qK
    {s : Finset W.I₀ // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty})) B
  let EK := @RetainedCharacter.fieldSchemeDiagram.{u,u,u} K (@Field.toCommRing K kField)
    (bsdhScheme G word) (bsdhToSpec G word) {s : Finset W.I₀ // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty})) V
  let F := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} K
    (@Field.toCommRing K kField) (bsdhScheme G word) (bsdhToSpec G word)
    {s : Finset W.I₀ // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty})) V
  let M := @FrobeniusSplitting.intersectionCoordinates.{u,u,u} S
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) S)
    Y base {s : Finset W.I₀ // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty})) B
  have hV : V = intersectionOpens O :=
    CategoryTheory.Functor.ext (fun s ↦ by
      change qK ⁻¹ᵁ (⨅ j ∈ s.unop.val, Wu j) = ⨅ j ∈ s.unop.val, qK ⁻¹ᵁ Wu j
      rw [← Finset.inf_eq_iInf, ← Finset.inf_eq_iInf]
      exact map_finset_inf qK.base.frameHom _ _) (fun _ _ _ ↦ Subsingleton.elim _ _)
  have hCoordinates := @prior_intersection_coordinates.{u} S K
    (inferInstanceAs (CommRing S)) (@Field.toCommRing K kField)
    (inferInstanceAs (Algebra S K)) Y (bsdhScheme G word) base baseProper
    (bsdhToSpec G word) qK hK W.I₀ Wu hWu
  obtain ⟨e, hpure, he⟩ := hCoordinates
  have hCocone := @open_diagram_coordinate_cocone.{u} K (@Field.toCommRing K kField)
    (bsdhScheme G word)
    (inferInstanceAs (IsAffineHom (pullback.diagonal (terminal.from (bsdhScheme G word)))))
    (bsdhToSpec G word) W.I₀ O hO hcover V hV
  obtain ⟨hEK, b, ⟨hb⟩, hbbase, hbleg, p, hp, hpn, hcommon⟩ := hCocone
  let bo (j : W.I₀) : Over.mk (U.f j ≫ bsdhToSpec G word) ⟶
      Over.mk (bsdhToSpec G word) := Over.homMk (U.f j) rfl
  obtain ⟨beta, _, hchart, hnatural, hbeta, _⟩ :=
    bsdh_transition_family (K := K) (J := W.I₀) G word i F
    (fun j ↦ Over.mk (U.f j ≫ bsdhToSpec G word)) bo p hpn hcommon g a ha c
    (fun j ↦ (hcart j).w) hend
  let sel (s : {s : Finset W.I₀ // s.Nonempty}) : {j : W.I₀ // j ∈ s.val} :=
    ⟨s.property.choose, s.property.choose_spec⟩
  have hProjection := @prior_bundle_projection.{u} K kField kClosed kZero
    G i S hS Y (bsdhScheme G word) base baseProper baseSmooth
    (bsdhToSpec G word) qK hK W.I₀ wFinite Wu hWu W.iSup_opensRange
    e hpure he hEK b hb hbleg sel beta hnatural hbeta
  obtain ⟨R, hSR, H⟩ := hProjection
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let N : {s : Finset W.I₀ // s.Nonempty} ⥤ CommAlgCat.{u} R :=
    fixedFibreDiagram (R := R) (M := R) M
  let eR := @scalarDiagramComparison.{u,u,u} K kField S R hSR
    {s : Finset W.I₀ // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty})) M F e
  let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let YR := pullback base sr
  let baseR := pullback.snd base sr
  let qR := pullback.fst base sr
  let : YR.IsSeparated := ⟨by rw [← terminal.comp_from baseR]; infer_instance⟩
  let VR := @RetainedCharacter.inverseOpenDiagram.{u,u,u} Y YR qR
    {s : Finset W.I₀ // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty})) B
  let ER := @RetainedCharacter.fieldSchemeDiagram.{u,u,u} R
    (@Subalgebra.toCommRing ℤ K Int.instCommRing (@Field.toCommRing K kField)
      (@Ring.toIntAlgebra K (@DivisionRing.toRing K (@Field.toDivisionRing K kField))) R)
    YR baseR {s : Finset W.I₀ // s.Nonempty}
    (inferInstanceAs (Category.{u} {s : Finset W.I₀ // s.Nonempty})) VR
  obtain ⟨hR, heR, hER, d, cG, hpt, ⟨hcG⟩, hproperBase, hBundle,
    m₀, hm₀, hmprior, hbmodel⟩ := H
  have hF : F = intersectionCoordinates (bsdhToSpec G word) (intersectionOpens O) :=
    congrArg (intersectionCoordinates (bsdhToSpec G word)) hV
  have hopenF := coordinate_diagram_opens (bsdhToSpec G word) O hO F (eqToIso hF)
  let nativeOpen : ∀ {s t : {s : Finset W.I₀ // s.Nonempty}} (f : s ⟶ t),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)) :=
    fun {s t} f ↦ hopenF.1 s t f
  let : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected := hopenF.2
  let UR := fun j ↦ qR ⁻¹ᵁ Wu j
  have hUR (j : W.I₀) : IsAffineOpen (UR j) := by
    let : IsAffine (Wu j).toScheme := hWu j
    exact IsAffine.of_isPullback
      ((isPullback_morphismRestrict qR (Wu j)).paste_vert (IsPullback.of_hasPullback base sr))
  have hopenN := opens_from_preimage_coordinates (R := R) baseR qR Wu hUR N d
  let modelOpen : ∀ {s t : {s : Finset W.I₀ // s.Nonempty}} (f : s ⟶ t),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom)) :=
    fun {s t} f ↦ hopenN.1 s t f
  let : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected := hopenN.2
  have hcomp (s : {s : Finset W.I₀ // s.Nonempty}) :=
    (refined_append_chart G word i (bo (sel s).val)
      (p s (sel s).val (sel s).property) (g (sel s).val) (a (sel s).val)
      (c (sel s).val) (hcart (sel s).val) (hend (sel s).val)).1
  have hcartNative (s : {s : Finset W.I₀ // s.Nonempty}) : IsPullback
      (fst ((algSpec (.of K)).obj (.op (F.obj s)))
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
      ((p s (sel s).val (sel s).property ⊗ₘ 𝟙 _) ≫ c (sel s).val).left
      (b.app (.op s)) (bsdhAppendFst G word i) :=
    (congrArg (fun z : Spec (.of (F.obj s)) ⟶ bsdhScheme G word ↦
      IsPullback
        (fst ((algSpec (.of K)).obj (.op (F.obj s)))
          (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left
        ((p s (sel s).val (sel s).property ⊗ₘ 𝟙 _) ≫ c (sel s).val).left
        z (bsdhAppendFst G word i)) (hp s (sel s).val (sel s).property)).mp (hcomp s)
  let q₀ : cG.pt.left ⟶ Y := (eqToIso hpt).hom.left ≫ qR
  have hprior : IsPullback q₀ cG.pt.hom base sr :=
    point_pullback base sr cG.pt (eqToIso hpt)
  have hsmoothR : Smooth baseR :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback base sr) (inferInstance : Smooth base)
  have hsmoothBase : Smooth cG.pt.hom := by
    rw [hpt]
    change Smooth baseR
    exact hsmoothR
  let : IsProper cG.pt.hom := hproperBase
  let : Smooth cG.pt.hom := hsmoothBase
  have step := @append_from_fixed_models K R
    (inferInstance : Field K) (inferInstance : IsAlgClosed K) (inferInstance : CharZero K)
    (inferInstance : CommRing R) (inferInstance : Algebra R K)
    G word i U F N eR heR nativeOpen hopenF.2 modelOpen hopenN.2
  have nativeStep := step p g a c ha hend
  have diagramStep := nativeStep hpn beta hchart hnatural hbeta
    sel b hb hp hbbase hcartNative
  have modelStep := diagramStep cG hcG m₀ hm₀ hbmodel
  have Happend := modelStep hBundle
  obtain ⟨Z, baseZ, q, m, hbaseZ, hproperZ, hsmoothZ, hproper, hsmooth, hgc,
    hmq, hm, hboundary⟩ := Happend
  exact ⟨R, hSR, hR, cG.pt.left, Z, cG.pt.hom, baseZ, q₀, q, m₀, m,
    hproperBase, hsmoothBase, hprior, hm₀, hmprior, hbaseZ,
    hproperZ, hsmoothZ, hproper, hsmooth, hgc, hmq, hm, hboundary⟩

end SchubertGeometry
