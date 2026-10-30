import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeScalarExtension
import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeChartPrimes

/-! # Coefficient stages of closed coordinate families -/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u v

open private retain_surjective_family from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixClosedTargets
open private extend_primitives tensor_surjective from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixCommonCoefficients
open private tensor_functor tensor_comparison tensor_comparison_natural
  tensor_map_hom tensor_open tensor_pushout scalar_flag from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates
open private coefficient_targets targets_from_stage later_surjective from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixStageCoordinates
open private quotient_component variety_diagonal retain_refinements from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets
open private stage_properties from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing
open private scalar_functor from
  OrbitComplexity.SchubertGeometry.Connectedness.AppendCellConnected

open private coconeCover from
  OrbitComplexity.FrobeniusSplitting.Normality.Covers.IntersectionModelCover

open private tensor_inclusion_cart from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FixedScalarCocone

open private coordinate_prime_stage from
  OrbitComplexity.SchubertGeometry.Normality.Components.OppositeChartPrimes

private theorem closed_coordinate_stage
    {K T I : Type u} [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    [hT : Finite T] [hI : Finite I]
    (G : ReductiveGroups.ReductiveGroupData K)
    (Z : I → TopologicalSpace.Closeds (flagVariety G).scheme)
    (U : T → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (S₀ : Subalgebra ℤ K) (hS₀ : S₀.FG)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    let C := {s : Finset T // s.Nonempty}
    let F := FrobeniusSplitting.intersectionCoordinates (flagVariety G).toSpec (intersectionOpens U)
    let j := fun i => (flagVariety G).closedInclusion (Z i)
    let B := fun i => FrobeniusSplitting.intersectionCoordinates
      ((j i).left ≫ (flagVariety G).toSpec) (intersectionOpens (fun t => (j i).left ⁻¹ᵁ U t))
    let A := (Sigma.desc B).sum' F
    let H : (Σ _ : I, C) ⥤ C :=
      Sigma.desc (fun _ => FrobeniusSplitting.intersectionIndexMap (id : T → T))
    ∃ (S : Subalgebra ℤ K) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
      (e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K] A.obj x)
      (β : H ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ N) ⟶
        Sum.inl_ (Σ _ : I, C) C ⋙ N),
      S.FG ∧ S₀ ≤ S ∧ start ≤ S ∧
      (∀ x, Algebra.FinitePresentation S (N.obj x)) ∧
      (∀ x y (a : x ⟶ y), (e y).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map a).hom) =
          (A.map a).hom.comp (e x).toAlgHom) ∧
      (∀ x : Σ _ : I, C, (e (.inl x)).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (β.app x).hom) =
          (((@intersectionCoordinateMap.{u}
            ((flagVariety G).closedSubvariety (Z x.1)).scheme
            (flagVariety G).scheme T T K hK.toCommRing (j x.1).left
            (flagVariety G).toSpec (fun t => (j x.1).left ⁻¹ᵁ U t)
            U id (fun _ => le_rfl)).app x.2).hom).comp
              (e (.inr (H.obj x))).toAlgHom) ∧
      (∀ x, Function.Surjective (β.app x).hom) ∧
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
          (CommRingCat.ofHom (N.map q).hom.toRingHom)  := by
  intro C F j B A H
  have models := @exists_closed_flag_models K T I hK hAlg hChar hT hI G Z U hU
  obtain ⟨S, N, e, β, hS, hfp, _hsmooth, hn, _hinj, hβ, hsurj, hopen, hpush⟩ := models
  have hfiniteB : ∀ x : Σ _ : I, C, Algebra.FiniteType S (N.obj (.inl x)) := by
    intro x
    have h := hfp (.inl x)
    infer_instance
  have retained := @retain_surjective_family K hK S hS (Σ _ : I, C)
    (inferInstance : Finite (Σ _ : I, C))
    (fun x => N.obj (.inr (H.obj x))) (fun x => N.obj (.inl x))
    (fun x => inferInstance) (fun x => inferInstance)
    (fun x => inferInstance) (fun x => inferInstance) hfiniteB
    (fun x => (β.app x).hom) hsurj
  obtain ⟨R, hSR, hR, hsurjR⟩ := retained
  let T₀ : Subalgebra ℤ K := R ⊔ (S₀ ⊔ start)
  have hRT : R ≤ T₀ := le_sup_left
  have hST : S ≤ T₀ := hSR.trans hRT
  have hS₀T : S₀ ≤ T₀ := le_sup_left.trans le_sup_right
  have hstartT : start ≤ T₀ := le_sup_right.trans le_sup_right
  have hTFG : T₀.FG := hR.sup (hS₀.sup hstart)
  let hSTAlgebra : Algebra S T₀ := (Subalgebra.inclusion hST).toAlgebra
  have hSTK : IsScalarTower S T₀ K :=
    Subalgebra.inclusion.isScalarTower_right hST K
  have hsurjT : ∀ x : Σ _ : I, C, Function.Surjective
      (Algebra.TensorProduct.lTensor (S := T₀) T₀ (β.app x).hom) :=
    fun x => @later_surjective K hK.toCommRing S ⟨R, hR, hSR⟩
      ⟨T₀, hTFG, hST⟩ hRT
      ((H ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ N)).obj x)
      ((Sum.inl_ (Σ _ : I, C) C ⋙ N).obj x) (β.app x) (hsurjR x)
  let δ : ((H ⋙ Sum.inr_ (Σ _ : I, C) C) ⋙ A) ⟶
      (Sum.inl_ (Σ _ : I, C) C ⋙ A) :=
    { app := fun x => (@intersectionCoordinateMap.{u}
            ((flagVariety G).closedSubvariety (Z x.1)).scheme
            (flagVariety G).scheme T T K hK.toCommRing (j x.1).left
        (flagVariety G).toSpec (fun t => (j x.1).left ⁻¹ᵁ U t)
        U id (fun _ => le_rfl)).app x.2
      naturality := by
        rintro ⟨i, s⟩ ⟨_, t⟩ ⟨a⟩
        exact (@intersectionCoordinateMap.{u}
            ((flagVariety G).closedSubvariety (Z i)).scheme
            (flagVariety G).scheme T T K hK.toCommRing (j i).left (flagVariety G).toSpec
          (fun t => (j i).left ⁻¹ᵁ U t) U id (fun _ => le_rfl)).naturality a }
  have properties := @extend_primitives S T₀ K
    (inferInstance : CommRing S) (inferInstance : CommRing T₀) hK.toCommRing
    hSTAlgebra (inferInstance : Algebra S K) (inferInstance : Algebra T₀ K) hSTK
    ((Σ _ : I, C) ⊕ C) (Σ _ : I, C)
    (inferInstance : Category ((Σ _ : I, C) ⊕ C))
    (inferInstance : Category (Σ _ : I, C))
    (H ⋙ Sum.inr_ (Σ _ : I, C) C) (Sum.inl_ (Σ _ : I, C) C)
    N A e β δ hfp hn hβ hsurjT hopen hpush
  obtain ⟨hfpT, hnT, hβT, hsurjT₀, hopenT, hpushT⟩ := properties
  exact ⟨T₀, N ⋙ tensor_functor S T₀,
    (fun x => tensor_comparison S T₀ (N.obj x) (A.obj x) (e x)),
    Functor.whiskerRight β (tensor_functor S T₀),
    hTFG, hS₀T, hstartT, hfpT, hnT, hβT, hsurjT₀, hopenT, hpushT⟩


open private CoordinateExtensionData.Properties extend_coordinate_properties from
  OrbitComplexity.SchubertGeometry.Normality.Components.OppositeScalarExtension

section CoordinateStage

variable {K T I : Type u} [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
  [hT : Finite T] [hI : Finite I] (G : ReductiveGroups.ReductiveGroupData K)
  (Z : I → TopologicalSpace.Closeds (flagVariety G).scheme)
  (U : T → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t))

set_option quotPrecheck false

local notation "C" => {s : Finset T // s.Nonempty}
local notation "F" => intersectionCoordinates (flagVariety G).toSpec (intersectionOpens U)
local notation "j" => (fun i => (flagVariety G).closedInclusion (Z i))
local notation "B" => (fun i => intersectionCoordinates
  ((j i).left ≫ (flagVariety G).toSpec) (intersectionOpens (fun t => (j i).left ⁻¹ᵁ U t)))
local notation "A" => (Sigma.desc B).sum' F
local notation "H" => Sigma.desc (fun _ : I => intersectionIndexMap (id : T → T))

/-- A coefficient model for a finite family of closed coordinate diagrams and its scalar fibre. -/
structure ClosedCoordinateStage (S₀ : Subalgebra ℤ K) (P : Over (Spec (.of S₀)))
    (qP : (flagVariety G).scheme ⟶ P.left) (start : CoefficientStage S₀) where
  /-- The coefficient subalgebra. -/
  S : Subalgebra ℤ K
  /-- Finite generation of the coefficient subalgebra. -/
  hS : S.FG
  /-- The initial coefficients lie in this subalgebra. -/
  hS₀S : S₀ ≤ S
  /-- The chosen starting stage lies in this subalgebra. -/
  hstartS : start.val ≤ S
  /-- The joint coefficient diagram. -/
  N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S
  /-- The generic-fibre algebra identifications. -/
  e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K] (A).obj x
  /-- The coefficient quotient transformation. -/
  β : H ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ N) ⟶ Sum.inl_ (Σ _ : I, C) C ⋙ N
  /-- Finite presentation of the coefficient rings. -/
  hfp : ∀ x, Algebra.FinitePresentation S (N.obj x)
  /-- Naturality of the algebra identifications. -/
  hn : ∀ x y (a : x ⟶ y), (e y).toAlgHom.comp
    (Algebra.TensorProduct.lTensor (S := K) K (N.map a).hom) =
      ((A).map a).hom.comp (e x).toAlgHom
  /-- The quotient maps agree with the closed immersions. -/
  hβ : ∀ x : Σ _ : I, C, (e (.inl x)).toAlgHom.comp
    (Algebra.TensorProduct.lTensor (S := K) K (β.app x).hom) =
      (((@intersectionCoordinateMap.{u}
        ((flagVariety G).closedSubvariety (Z x.1)).scheme
        (flagVariety G).scheme T T K hK.toCommRing (j x.1).left
        (flagVariety G).toSpec (fun t => (j x.1).left ⁻¹ᵁ U t)
        U id (fun _ => le_rfl)).app x.2).hom).comp (e (.inr ((H).obj x))).toAlgHom
  /-- The coefficient quotient maps are surjective. -/
  hsurj : ∀ x, Function.Surjective (β.app x).hom
  /-- The coefficient charts have open transition maps. -/
  hopen : ∀ x y (a : x ⟶ y), IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (N.map a).hom.toRingHom))
  /-- The coefficient diagram preserves the chart pushout squares. -/
  hpush : ∀ (x y z t) (a : x ⟶ y) (b : x ⟶ z) (p : y ⟶ t) (q : z ⟶ t),
    IsPushout (CommRingCat.ofHom ((A).map a).hom.toRingHom)
      (CommRingCat.ofHom ((A).map b).hom.toRingHom)
      (CommRingCat.ofHom ((A).map p).hom.toRingHom)
      (CommRingCat.ofHom ((A).map q).hom.toRingHom) →
    IsPushout (CommRingCat.ofHom (N.map a).hom.toRingHom)
      (CommRingCat.ofHom (N.map b).hom.toRingHom)
      (CommRingCat.ofHom (N.map p).hom.toRingHom)
      (CommRingCat.ofHom (N.map q).hom.toRingHom)
  /-- The generic projection to the prescribed flag model. -/
  qPS : (flagVariety G).scheme ⟶ (stageScalarModel S₀ P.hom ⟨S, hS, hS₀S⟩).left
  /-- The projection square to the prescribed flag model is Cartesian. -/
  hPS : IsPullback qPS (flagVariety G).toSpec
    (stageScalarModel S₀ P.hom ⟨S, hS, hS₀S⟩).hom
    (Spec.map (CommRingCat.ofHom (algebraMap S K)))
  /-- The coefficient triangle of the prescribed flag model. -/
  hfirst : qPS ≫ pullback.fst
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀S).toRingHom)) P.hom =
      (flagVariety G).toSpec ≫ Spec.map (CommRingCat.ofHom (algebraMap S K))
  /-- The generic projection is the prescribed map. -/
  hsecond : qPS ≫ pullback.snd
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀S).toRingHom)) P.hom = qP
  /-- The coefficient stage for the chosen target family. -/
  k : CoefficientStage S
  /-- The chosen flag and closed target models. -/
  targets : @coefficient_targets (flagVariety G).scheme T I K hK.toCommRing
    (@variety_diagonal K hK (flagVariety G))
    (fun i => ((flagVariety G).closedSubvariety (Z i)).scheme)
    (fun i => @variety_diagonal K hK ((flagVariety G).closedSubvariety (Z i)))
    (fun i => (j i).left) (fun i => (inferInstance : IsClosedImmersion (j i).left))
    (flagVariety G).toSpec U hU S N e β
    (stageScalarModel S₀ P.hom ⟨S, hS, hS₀S⟩) qPS k
  /-- Surjectivity after the coefficient extension. -/
  hsurjK : let _ : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
    ∀ x, Function.Surjective (Algebra.TensorProduct.lTensor (S := k.val) k.val (β.app x).hom)
  /-- Cartesian chart squares after the coefficient extension. -/
  hcartK : let _ : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
    ∀ a, (Functor.whiskerRight
      (NatTrans.op (quotient_component (intersectionIndexMap (id : T → T)) N β a))
      (algSpec (.of S) ⋙ scalar_functor
        (Spec.map (CommRingCat.ofHom (algebraMap S k.val))) ⋙ Over.forget _)).Equifibered
  /-- The coordinate and atlas properties after the coefficient extension. -/
  scalarProperties :
    let hSk : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
    let hSkK : IsScalarTower S k.val K := Subalgebra.inclusion.isScalarTower_right k.property.2 K
    @CoordinateExtensionData.Properties.{u} K hK.toCommRing {
      I := I, «C» := C, categoryC := @Preorder.smallCategory C
        (@Subtype.preorder (Finset T)
          (@PartialOrder.toPreorder (Finset T) (@Finset.instPartialOrder T))
          (fun s : Finset T => s.Nonempty))
      S := S, R := k.val, algebraSR := hSk, towerSRK := hSkK
      «H» := intersectionIndexMap (id : T → T), «F» := F, «B» := B
      d := fun x => (@intersectionCoordinateMap.{u}
        ((flagVariety G).closedSubvariety (Z x.1)).scheme
        (flagVariety G).scheme T T K hK.toCommRing (j x.1).left
        (flagVariety G).toSpec (fun t => (j x.1).left ⁻¹ᵁ U t) U id (fun _ => le_rfl)).app x.2
      N := N, e := e, β := β, hfp := hfp, hn := hn, hβ := hβ
      hsurj := hsurjK, hopen := hopen, hpush := hpush }

end CoordinateStage

private theorem closed_target_stage
    {K T I : Type u} [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    [hT : Finite T] [hI : Finite I]
    (G : ReductiveGroups.ReductiveGroupData K)
    (Z : I → TopologicalSpace.Closeds (flagVariety G).scheme)
    (U : T → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (hcover : (⨆ t, U t) = ⊤)
    (S₀ : Subalgebra ℤ K) (hS₀ : S₀.FG) (P : Over (Spec (.of S₀)))
    [hPCompact : CompactSpace P.left] [hPFP : LocallyOfFinitePresentation P.hom]
    (qP : (flagVariety G).scheme ⟶ P.left)
    (hP : IsPullback qP (flagVariety G).toSpec P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
    (start : CoefficientStage S₀) :
    Nonempty (ClosedCoordinateStage G Z U hU S₀ P qP start) := by
  let C := {s : Finset T // s.Nonempty}
  let F := intersectionCoordinates (flagVariety G).toSpec (intersectionOpens U)
  let j := fun i => (flagVariety G).closedInclusion (Z i)
  let B := fun i => intersectionCoordinates
    ((j i).left ≫ (flagVariety G).toSpec) (intersectionOpens (fun t => (j i).left ⁻¹ᵁ U t))
  let A := (Sigma.desc B).sum' F
  let H : (Σ _ : I, C) ⥤ C := Sigma.desc (fun _ => intersectionIndexMap (id : T → T))
  have coordinates := @closed_coordinate_stage K T I hK hAlg hChar hT hI
    G Z U hU S₀ hS₀ start.val start.property.1
  obtain ⟨S, N, e, β, hS, hS₀S, hstartS, hfp, hn, hβ, hsurj, hopen, hpush⟩ := coordinates
  let hS₀SAlgebra : Algebra S₀ S := (Subalgebra.inclusion hS₀S).toAlgebra
  have hS₀SK : IsScalarTower S₀ S K :=
    Subalgebra.inclusion.isScalarTower_right hS₀S K
  have scalar := @scalar_flag S₀ S
    (inferInstance : CommRing S₀) (inferInstance : CommRing S) hS₀SAlgebra
    K hK.toCommRing (inferInstance : Algebra S₀ K) (inferInstance : Algebra S K)
    hS₀SK P (flagVariety G).toOver qP hP
  obtain ⟨qPS, hPS, hfirst, hsecond⟩ := scalar
  have hPprops := @stage_properties K hK.toCommRing S₀ hS₀ P hPCompact hPFP
    ⟨S, hS, hS₀S⟩
  have hsurjS : ∀ x : Σ _ : I, C, Function.Surjective
      (Algebra.TensorProduct.lTensor (S := S) S (β.app x).hom) :=
    fun x => @tensor_surjective S (inferInstance : CommRing S)
      ((H ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ N)).obj x)
      ((Sum.inl_ (Σ _ : I, C) C ⋙ N).obj x) (β.app x) (hsurj x)
  have targets := @coordinate_prime_stage (flagVariety G).scheme T I K hK.toCommRing hT hI
    (@variety_diagonal K hK (flagVariety G))
    (fun i => ((flagVariety G).closedSubvariety (Z i)).scheme)
    (fun i => @variety_diagonal K hK ((flagVariety G).closedSubvariety (Z i)))
    (fun i => (j i).left)
    (fun i => (inferInstance : IsClosedImmersion (j i).left))
    (flagVariety G).toSpec U hU hcover S N e β hS hfp hn hβ hopen hpush
    ⟨S, hS, le_rfl⟩ hsurjS
    (stageScalarModel S₀ P.hom ⟨S, hS, hS₀S⟩)
    hPprops.2.1 hPprops.2.2 hPprops.1 qPS hPS
  obtain ⟨k, _hstartK, htargets, hsurjK, hcartK⟩ := targets
  let hSk : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
  let hSkK : IsScalarTower S k.val K := Subalgebra.inclusion.isScalarTower_right k.property.2 K
  let scalarData : @CoordinateExtensionData.{u} K hK.toCommRing := {
    I := I, C := C, categoryC := @Preorder.smallCategory C
      (@Subtype.preorder (Finset T)
        (@PartialOrder.toPreorder (Finset T) (@Finset.instPartialOrder T))
        (fun s : Finset T => s.Nonempty))
    S := S, R := k.val, algebraSR := hSk, towerSRK := hSkK
    H := intersectionIndexMap (id : T → T), F := F, B := B
    d := fun x => (@intersectionCoordinateMap.{u}
      ((flagVariety G).closedSubvariety (Z x.1)).scheme
      (flagVariety G).scheme T T K hK.toCommRing (j x.1).left
      (flagVariety G).toSpec (fun t => (j x.1).left ⁻¹ᵁ U t) U id (fun _ => le_rfl)).app x.2
    N := N, e := e, β := β, hfp := hfp, hn := hn, hβ := hβ
    hsurj := hsurjK, hopen := hopen, hpush := hpush }
  have properties := @extend_coordinate_properties.{u} K hK.toCommRing scalarData
  exact ⟨{
    S := S, hS := hS, hS₀S := hS₀S, hstartS := hstartS
    N := N, e := e, β := β, hfp := hfp, hn := hn, hβ := hβ
    hsurj := hsurj, hopen := hopen, hpush := hpush
    qPS := qPS, hPS := hPS, hfirst := hfirst, hsecond := hsecond
    k := k, targets := htargets, hsurjK := hsurjK, hcartK := hcartK
    scalarProperties := properties }⟩

end SchubertGeometry
