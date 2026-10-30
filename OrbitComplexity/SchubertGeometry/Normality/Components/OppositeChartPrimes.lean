import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeClosedPrimes
import OrbitComplexity.ReductiveGroups.Groups.Representatives.WeylRepresentativeAbstract
import OrbitComplexity.SchubertGeometry.Normality.Coordinates.ChosenClosedInclusion
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordRawIdeals
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.IntersectionModelCover
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FixedScalarCocone
import OrbitComplexity.FrobeniusSplitting.Normality.GluedFiniteness
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Prime kernels on affine charts of opposite Schubert models -/

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


private theorem ideal_top_or_prime_of_comap
    {R A : Type u} [CommRing R] [CommRing A] (I : Ideal R) (e : R ≃+* A)
    (h : I.comap e.symm.toRingHom = ⊤ ∨ (I.comap e.symm.toRingHom).IsPrime) :
    I = ⊤ ∨ I.IsPrime := by
  rcases h with h | h
  · exact Or.inl (Ideal.comap_eq_top_iff.mp h)
  · have hprime : (I.comap e.symm.toRingHom).IsPrime := h
    have reflected : ((I.comap e.symm.toRingHom).comap e.toRingHom).IsPrime :=
      Ideal.comap_isPrime e.toRingHom _
    have hcomp : e.symm.toRingHom.comp e.toRingHom = RingHom.id R :=
      RingHom.ext fun x => e.symm_apply_apply x
    exact Or.inr (by
      simpa only [Ideal.comap_comap, hcomp, Ideal.comap_id] using reflected)

private theorem chart_kernel_top_or_prime
    {R A : Type u} [CommRing R] [CommRing A] (g : R →+* A)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [QuasiCompact j]
    (a : Spec (.of A) ⟶ X) (b : Spec (.of R) ⟶ Y) [IsOpenImmersion b]
    (hcart : IsPullback (Spec.map (CommRingCat.ofHom g)) a b j)
    (hprime : ∀ U : Y.affineOpens, j.ker.ideal U = ⊤ ∨ (j.ker.ideal U).IsPrime) :
    RingHom.ker g = ⊤ ∨ (RingHom.ker g).IsPrime := by
  have hchart : (Spec.map (CommRingCat.ofHom g)).ker.ideal
      ⟨⊤, isAffineOpen_top (Spec (.of R))⟩ = ⊤ ∨
      ((Spec.map (CommRingCat.ofHom g)).ker.ideal
        ⟨⊤, isAffineOpen_top (Spec (.of R))⟩).IsPrime := by
    rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion j
      (Spec.map (CommRingCat.ofHom g)) a b hcart]
    rcases hprime _ with h | h
    · exact Or.inl (by rw [h, Ideal.comap_top])
    · have hp : (j.ker.ideal
          ⟨b ''ᵁ ⊤, (isAffineOpen_top (Spec (.of R))).image_of_isOpenImmersion b⟩).IsPrime := h
      exact Or.inr (Ideal.comap_isPrime _ _)
  have heq : (Spec.map (CommRingCat.ofHom g)).ker.ideal
      ⟨⊤, isAffineOpen_top (Spec (.of R))⟩ =
      (RingHom.ker g).comap (StructureSheaf.globalSectionsIso R).inv.hom := by
    simpa [Scheme.ker_of_isAffine] using
      FrobeniusSplitting.spec_kernel g
  rw [heq] at hchart
  exact ideal_top_or_prime_of_comap (RingHom.ker g)
    (StructureSheaf.globalSectionsIso R).commRingCatIsoToRingEquiv hchart


private theorem kernel_top_or_prime_of_open
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B)
    {X : Scheme.{u}} (b : Spec (.of B) ⟶ X) [IsOpenImmersion b]
    (h : ∀ U : X.affineOpens, (𝟙 X : X ⟶ X).ker.ideal U = ⊤ ∨
      ((𝟙 X : X ⟶ X).ker.ideal U).IsPrime) :
    RingHom.ker g = ⊤ ∨ (RingHom.ker g).IsPrime := by
  have hsquare : IsPullback (Spec.map (CommRingCat.ofHom (RingHom.id B))) b b (𝟙 X) := by
    simpa only [CommRingCat.ofHom_id, Spec.map_id] using
      (IsPullback.of_id_fst (f := b))
  have hid := chart_kernel_top_or_prime (RingHom.id B) (𝟙 X) b b hsquare h
  have hker : RingHom.ker g = (RingHom.ker (RingHom.id B)).comap g := rfl
  rcases hid with htop | hprime
  · exact Or.inl (by rw [hker, htop, Ideal.comap_top])
  · have hp : (RingHom.ker (RingHom.id B)).IsPrime := hprime
    apply Or.inr
    rw [hker]
    exact Ideal.comap_isPrime g _

private theorem chart_pullback
    {C : Type u} [Category.{v} C] {A B X Y T S : C}
    (qA : A ⟶ B) (a : A ⟶ T) (b : B ⟶ S) (s : T ⟶ S)
    (qX : X ⟶ Y) (x : X ⟶ T) (y : Y ⟶ S) (j : B ⟶ Y)
    (hj : j ≫ y = b) (hA : IsPullback qA a b s)
    (hX : IsPullback qX x y s) :
    ∃ k : A ⟶ X, IsPullback qA k j qX := by
  have hsquare : (qA ≫ j) ≫ y = a ≫ s :=
    (Category.assoc qA j y).trans ((congrArg (fun z => qA ≫ z) hj).trans hA.w)
  let k : A ⟶ X := hX.lift (qA ≫ j) a hsquare
  have hk : k ≫ qX = qA ≫ j := hX.lift_fst _ _ _
  have hb : k ≫ x = a := hX.lift_snd _ _ _
  have houter : IsPullback qA (k ≫ x) (j ≫ y) s := by
    rw [hb, hj]
    exact hA
  exact ⟨k, houter.of_bot hk.symm hX⟩

private theorem tensor_chart_kernel
    {R L A : Type u} [CommRing R] [Field L] [CommRing A] [Algebra R L]
    (M : CommAlgCat.{u} R) (g : A →+* L ⊗[R] M) (D : Over (Spec (.of R)))
    (j : (algSpec (.of R)).obj (op M) ⟶ D)
    [IsOpenImmersion j.left]
    (X : Over (Spec (.of L))) (qX : X.left ⟶ D.left)
    (hX : IsPullback qX X.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (hprime : ∀ U : X.left.affineOpens,
      (𝟙 X.left : X.left ⟶ X.left).ker.ideal U = ⊤ ∨ ((𝟙 X.left : X.left ⟶ X.left).ker.ideal
        U).IsPrime) :
    RingHom.ker g = ⊤ ∨ (RingHom.ker g).IsPrime := by
  have hA := @tensor_inclusion_cart R L M
    (inferInstance : CommRing R) (inferInstance : CommRing L)
    (inferInstance : CommRing M) (inferInstance : Algebra R L)
    (inferInstance : Algebra R M)
  obtain ⟨k, hk⟩ := chart_pullback
    (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : M →ₐ[R] L ⊗[R] M).toRingHom))
    (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[R] M))))
    (Spec.map (CommRingCat.ofHom (algebraMap R M)))
    (Spec.map (CommRingCat.ofHom (algebraMap R L)))
    qX X.hom D.hom j.left j.w hA hX
  have hopen : IsOpenImmersion k :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hk
      (inferInstance : IsOpenImmersion j.left)
  exact kernel_top_or_prime_of_open g k hprime

private theorem algebra_colimit_properties
    {R : Type u} [CommRing R] {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    [Finite C] (D : C ⥤ CommAlgCat.{u} R)
    [∀ c, Algebra.FinitePresentation R (D.obj c)]
    [∀ {c d} (f : c ⟶ d), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]
    [hdir : ((D.op ⋙ algSpec (.of R) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected]
    (c : Cocone (D.op ⋙ algSpec (.of R))) (hc : IsColimit c) :
    CompactSpace c.pt.left ∧ LocallyOfFinitePresentation c.pt.hom ∧
      ∀ s, IsOpenImmersion (c.ι.app s).left := by
  have hopen {s t : Cᵒᵖ} (a : s ⟶ t) :
      IsOpenImmersion (((D.op ⋙ algSpec (.of R)).map a).left) :=
    inferInstanceAs (IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (D.map a.unop).hom.toRingHom)))
  have haffine (s : Cᵒᵖ) : IsAffine ((D.op ⋙ algSpec (.of R)).obj s).left :=
    inferInstanceAs (IsAffine (Spec (.of (D.obj s.unop))))
  have hfp (s : Cᵒᵖ) : LocallyOfFinitePresentation
      ((D.op ⋙ algSpec (.of R)).obj s).hom := by
    change LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (D.obj s.unop))))
    apply (LocallyOfFinitePresentation.SpecMap_iff
      (CommRingCat.ofHom (algebraMap R (D.obj s.unop)))).mpr
    change (algebraMap R (D.obj s.unop)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  have hFinite : Finite Cᵒᵖ := Finite.of_injective Opposite.unop Opposite.unop_injective
  have hdir' : (((D.op ⋙ algSpec (.of R)) ⋙ Over.forget _) ⋙
      Scheme.forget).IsLocallyDirected := hdir
  have {s t : Cᵒᵖ} (a : s ⟶ t) :
      IsOpenImmersion (((D.op ⋙ algSpec (.of R)) ⋙ Over.forget _).map a) := hopen a
  have properties := finite_affine_colimit_properties (D.op ⋙ algSpec (.of R)) c hc
  refine ⟨properties.1, properties.2, ?_⟩
  intro s
  exact (coconeCover ((D.op ⋙ algSpec (.of R)) ⋙ Over.forget _)
    ((Over.forget _).mapCocone c) (isColimitOfPreserves (Over.forget _) hc)).map_prop s

private theorem finite_closed_prime_stage
    {K I : Type u} [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    [Finite I] (G : ReductiveGroups.ReductiveGroupData K)
    (word : I → List G.rootBase.support)
    (hred : ∀ i, (weylCoxeterSystem G.rootBase).IsReduced (word i))
    (S : Subalgebra ℤ K) (hS : S.FG) (D : I → Over (Spec (.of S)))
    (hfp : ∀ i, LocallyOfFinitePresentation (D i).hom)
    (hcompact : ∀ i, CompactSpace (D i).left)
    (qD : ∀ i, (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase (word i))).toOver.left ⟶ (D i).left)
    (hD : ∀ i, IsPullback (qD i)
      (oppositeSchubertVariety G
        (G.longestElement * simpleWeylWord G.rootBase (word i))).toOver.hom
      (D i).hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ R : CoefficientStage S, start ≤ R ∧
      ∀ (L : Type u) [Field L] [Algebra R.val L] (i : I)
        (YL : Over (Spec (.of L))) (qYL : YL.left ⟶ (D i).left)
        (_hYL : IsPullback qYL YL.hom (D i).hom
          (Spec.map (CommRingCat.ofHom
            ((algebraMap R.val L).comp (Subalgebra.inclusion R.property.2).toRingHom))))
        (Z : Scheme.{u}) (j : YL.left ⟶ Z) (U : Z.affineOpens),
        j.ker.ideal U = ⊤ ∨ (j.ker.ideal U).IsPrime := by
  classical
  have hex (i : I) : ∃ R : CoefficientStage S, start.val ≤ R.val ∧
      ∀ (L : Type u) [Field L] [Algebra R.val L]
        (YL : Over (Spec (.of L))) (qYL : YL.left ⟶ (D i).left)
        (_hYL : IsPullback qYL YL.hom (D i).hom
          (Spec.map (CommRingCat.ofHom
            ((algebraMap R.val L).comp (Subalgebra.inclusion R.property.2).toRingHom))))
        (Z : Scheme.{u}) (j : YL.left ⟶ Z) (U : Z.affineOpens),
        j.ker.ideal U = ⊤ ∨ (j.ker.ideal U).IsPrime := by
    have data := @exists_opposite_closed_primes K hK hAlg hChar G (word i) (hred i)
      S hS (D i) (hfp i) (hcompact i) (qD i) (hD i) start.val start.property.1
    obtain ⟨R, hR, hstartR, hSR, hprime⟩ := data
    refine ⟨⟨R, hR, hSR⟩, hstartR, ?_⟩
    intro L hL hRL YL qYL hYL
    exact (@hprime L hL hRL YL qYL hYL).2
  choose stage _hstartStage hprime using hex
  let stages : Option I → CoefficientStage S := fun i =>
    i.elim start stage
  have hNonempty : Nonempty (CoefficientStage S) := ⟨start⟩
  obtain ⟨R, hR⟩ := (Set.finite_range stages).bddAbove
  have hstartR : start ≤ R := hR ⟨none, rfl⟩
  refine ⟨R, hstartR, ?_⟩
  intro L hL hRL i YL qYL hYL Z j U
  have hiR : stage i ≤ R := hR ⟨some i, rfl⟩
  let hiL : Algebra (stage i).val L :=
    ((algebraMap R.val L).comp (Subalgebra.inclusion hiR).toRingHom).toAlgebra
  have hbase : (algebraMap (stage i).val L).comp
      (Subalgebra.inclusion (stage i).property.2).toRingHom =
      (algebraMap R.val L).comp (Subalgebra.inclusion R.property.2).toRingHom :=
    RingHom.ext fun _ => rfl
  have hYLi : IsPullback qYL YL.hom (D i).hom
      (Spec.map (CommRingCat.ofHom ((algebraMap (stage i).val L).comp
        (Subalgebra.inclusion (stage i).property.2).toRingHom))) := by
    rw [hbase]
    exact hYL
  exact @hprime i L hL hiL YL qYL hYLi Z j U

private theorem opposite_colimit_prime_stage
    {K C I : Type u} [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    [Category.{u} C] [Quiver.IsThin C] [Finite C] [Finite I]
    (G : ReductiveGroups.ReductiveGroupData K) (word : I → List G.rootBase.support)
    (hred : ∀ i, (weylCoxeterSystem G.rootBase).IsReduced (word i))
    (S : Subalgebra ℤ K) (hS : S.FG)
    (F₀ : C ⥤ CommAlgCat.{u} S) (B₀ : I → C ⥤ CommAlgCat.{u} S)
    (β₀ : ∀ i, F₀ ⟶ B₀ i)
    [∀ i c, Algebra.FinitePresentation S ((B₀ i).obj c)]
    [∀ i {c d} (f : c ⟶ d), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((B₀ i).map f).hom.toRingHom))]
    [∀ i, (((B₀ i).op ⋙ algSpec (.of S) ⋙ Over.forget _) ⋙
      Scheme.forget).IsLocallyDirected]
    (cBM : ∀ i, Cocone ((B₀ i).op ⋙ algSpec (.of S)))
    (hcBM : ∀ i, IsColimit (cBM i))
    (qD : ∀ i, (oppositeSchubertVariety G
      (G.longestElement * simpleWeylWord G.rootBase (word i))).toOver.left ⟶
      (cBM i).pt.left)
    (hD : ∀ i, IsPullback (qD i)
      (oppositeSchubertVariety G
        (G.longestElement * simpleWeylWord G.rootBase (word i))).toOver.hom
      (cBM i).pt.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (start : CoefficientStage S) :
    ∃ R : CoefficientStage S, start ≤ R ∧
      ∀ (L : Type u) [Field L] [Algebra R.val L],
        let _ : Algebra S L := ((algebraMap R.val L).comp
          (Subalgebra.inclusion R.property.2).toRingHom).toAlgebra
        ∀ i c, RingHom.ker
          (Algebra.TensorProduct.lTensor (S := L) L ((β₀ i).app c).hom).toRingHom = ⊤ ∨
          (RingHom.ker
            (Algebra.TensorProduct.lTensor (S := L) L ((β₀ i).app c).hom).toRingHom).IsPrime := by
  have properties (i : I) := algebra_colimit_properties (B₀ i) (cBM i) (hcBM i)
  have data := @finite_closed_prime_stage K I hK hAlg hChar
    (inferInstance : Finite I) G word hred S hS (fun i => (cBM i).pt)
    (fun i => (properties i).2.1) (fun i => (properties i).1) qD hD start
  obtain ⟨R, hstartR, hprime⟩ := data
  refine ⟨R, hstartR, ?_⟩
  intro L hL hRL hSL i c
  let τ := Spec.map (CommRingCat.ofHom (algebraMap S L))
  let X : Over (Spec (.of L)) := (scalar_functor τ).obj (cBM i).pt
  have hX : IsPullback (pullback.snd τ (cBM i).pt.hom) X.hom
      (cBM i).pt.hom τ := (IsPullback.of_hasPullback τ (cBM i).pt.hom).flip
  have hprimeX (U : X.left.affineOpens) :
      (𝟙 X.left : X.left ⟶ X.left).ker.ideal U = ⊤ ∨
      ((𝟙 X.left : X.left ⟶ X.left).ker.ideal U).IsPrime :=
    @hprime L hL hRL i X (pullback.snd τ (cBM i).pt.hom) hX
      X.left (𝟙 X.left) U
  have result := @tensor_chart_kernel S L (L ⊗[S] F₀.obj c)
    (inferInstance : CommRing S) hL (inferInstance : CommRing (L ⊗[S] F₀.obj c)) hSL
    ((B₀ i).obj c)
    (Algebra.TensorProduct.lTensor (S := L) L ((β₀ i).app c).hom).toRingHom
    (cBM i).pt ((cBM i).ι.app (op c)) ((properties i).2.2 (op c))
    X (pullback.snd τ (cBM i).pt.hom) hX hprimeX
  exact result

private theorem coordinate_prime_stage
    {Y : Scheme.{u}} {T I K : Type u} [hK : CommRing K] [hT : Finite T] [hI : Finite I]
    [hY : IsAffineHom (pullback.diagonal (terminal.from Y))]
    (X : I → Scheme.{u}) [hX : ∀ i, IsAffineHom (pullback.diagonal (terminal.from (X i)))]
    (j : ∀ i, X i ⟶ Y) [hj : ∀ i, IsClosedImmersion (j i)]
    (base : Y ⟶ Spec (.of K)) (U : T → Y.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (hcover : (⨆ t, U t) = ⊤) :
    let C := {s : Finset T // s.Nonempty}
    let H₀ := intersectionIndexMap (id : T → T)
    let H : (Σ _ : I, C) ⥤ C := Sigma.desc (fun _ => H₀)
    let F := intersectionCoordinates base (intersectionOpens U)
    let B := fun i => intersectionCoordinates (j i ≫ base) (intersectionOpens (fun t => j i ⁻¹ᵁ U
      t))
    let A := (Sigma.desc B).sum' F
    ∀ (S : Subalgebra ℤ K) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
      (e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K] A.obj x)
      (β : H ⋙ (Sum.inr_ _ _ ⋙ N) ⟶ Sum.inl_ _ _ ⋙ N),
      S.FG → (∀ x, Algebra.FinitePresentation S (N.obj x)) →
      (∀ x y (a : x ⟶ y), (e y).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map a).hom) =
        (A.map a).hom.comp (e x).toAlgHom) →
      (∀ x : Σ _ : I, C, (e (.inl x)).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (β.app x).hom) =
        ((intersectionCoordinateMap (j x.1) base (fun t => j x.1 ⁻¹ᵁ U t) U id
          (fun _ => le_rfl)).app x.2).hom.comp (e (.inr (H.obj x))).toAlgHom) →
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
      ∀ (i : CoefficientStage S),
        let _ : Algebra S i.val := (Subalgebra.inclusion i.property.2).toAlgebra
        (∀ x, Function.Surjective
          (Algebra.TensorProduct.lTensor (S := i.val) i.val (β.app x).hom)) →
        ∀ (P : Over (Spec (.of S))) [CompactSpace P.left] [QuasiSeparatedSpace P.left]
          [LocallyOfFinitePresentation P.hom] (qP : Y ⟶ P.left),
          IsPullback qP base P.hom
            (Spec.map (CommRingCat.ofHom (algebraMap S K))) →
          ∃ (k : CoefficientStage S), i ≤ k ∧
            coefficient_targets X j base U hU S N e β P qP k ∧
            let _ : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
            (∀ x, Function.Surjective
              (Algebra.TensorProduct.lTensor (S := k.val) k.val (β.app x).hom)) ∧
            (∀ a, (Functor.whiskerRight
              (NatTrans.op (quotient_component (intersectionIndexMap (id : T → T)) N β a))
              (algSpec (.of S) ⋙ scalar_functor
                (Spec.map (CommRingCat.ofHom (algebraMap S k.val))) ⋙
                Over.forget _)).Equifibered)  := by
  intro C H₀ H F B A S N e β hS hfp hn hβ hopen hpush i hSi hsurj
    P hPCompact hPQS hPFP qP hP
  have squares := @exists_prefix_chart_squares K T I hK hT hI Y X hY hX j hj
    base U hU S N e β hS hfp hn hβ i
  obtain ⟨k, hik, hsquares⟩ := squares
  let hSk : Algebra S k.val := (Subalgebra.inclusion k.property.2).toAlgebra
  have hsurjK : ∀ x, Function.Surjective
      (Algebra.TensorProduct.lTensor (S := k.val) k.val (β.app x).hom) :=
    fun x => @later_surjective K hK S i k hik
      ((Sigma.desc (fun _ : I => intersectionIndexMap (id : T → T)) ⋙
        (Sum.inr_ (Σ _ : I, {s : Finset T // s.Nonempty})
          {s : Finset T // s.Nonempty} ⋙ N)).obj x)
      ((Sum.inl_ (Σ _ : I, {s : Finset T // s.Nonempty})
        {s : Finset T // s.Nonempty} ⋙ N).obj x)
      (β.app x) (hsurj x)
  have hcartK : ∀ a, (Functor.whiskerRight
      (NatTrans.op (quotient_component (intersectionIndexMap (id : T → T)) N β a))
      (algSpec (.of S) ⋙ scalar_functor
        (Spec.map (CommRingCat.ofHom (algebraMap S k.val))) ⋙
        Over.forget _)).Equifibered := by
    intro a s t f
    exact hsquares a s t f
  have targets := @targets_from_stage Y T I K hK hT hY X hX j hj
    base U hU hcover S N e β hS hfp hn hβ hopen hpush k hsurjK hcartK
    P hPCompact hPQS hPFP qP hP
  exact ⟨k, hik, targets, hsurjK, hcartK⟩



end SchubertGeometry
