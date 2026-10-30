import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeScalarExtension
import OrbitComplexity.FrobeniusSplitting.Normality.EquifiberedColimits
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.IntersectionModelCover
import OrbitComplexity.FrobeniusSplitting.Normality.Components.MinimalPrimeFamilies
import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeComponentKernels
import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeCoordinateStages

/-! # Scalar extensions of closed coordinate diagrams -/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

open private scalar_kernel_sup from
  OrbitComplexity.SchubertGeometry.Normality.Components.OppositeComponentKernels

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

open private opposite_colimit_prime_stage from
  OrbitComplexity.SchubertGeometry.Normality.Components.OppositeChartPrimes
open private closed_target_stage from
  OrbitComplexity.SchubertGeometry.Normality.Components.OppositeCoordinateStages

/-- One coefficient enlargement retains all higher components and the
distinguished member of a finite family of quotient algebras. -/
private theorem component_stage
    {K W C : Type u} [hK : Field K] [Finite W] [Finite C]
    (S : Subalgebra ℤ K) (hS : S.FG)
    (A : C → CommAlgCat.{u} S) (B : W → C → CommAlgCat.{u} S)
    (f : ∀ w c, A c →ₐ[S] B w c)
    (hfpA : ∀ c, Algebra.FinitePresentation S (A c))
    (hfpB : ∀ w c, Algebra.FinitePresentation S (B w c))
    (hsurj : ∀ w c, Function.Surjective (f w c)) (rank : W → ℕ) (z : W)
    (hhigh : ∀ w, 2 ≤ rank w → ∃ a b, rank a < rank w ∧ rank b < rank w ∧
      ∀ c, RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f w c)).toRingHom = ⊤ ∨
        RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f w c)).toRingHom ∈
          ((RingHom.ker (f a c).toRingHom ⊔ RingHom.ker (f b c).toRingHom).map
            (Algebra.TensorProduct.includeRight : A c →ₐ[S] K ⊗[S] A c).toRingHom).minimalPrimes)
    (hzero : ∀ c,
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f z c)).toRingHom = ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (f z c)).toRingHom ∈
        (⊥ : Ideal _).minimalPrimes) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T), T.FG ∧
      ∀ (L : Type u) [Field L] [Algebra T L],
        letI : Algebra S L := ((algebraMap T L).comp
          (Subalgebra.inclusion hST).toRingHom).toAlgebra
        (∀ w c, RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f w c)).toRingHom = ⊤ ∨
          (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f w c)).toRingHom).IsPrime) →
        (∀ w, 2 ≤ rank w → ∃ a b, rank a < rank w ∧ rank b < rank w ∧
          ∀ c, RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f w c)).toRingHom = ⊤ ∨
            RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f w c)).toRingHom ∈
              (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f a c)).toRingHom ⊔
                RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f b
                  c)).toRingHom).minimalPrimes) ∧
        (∀ c, RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f z c)).toRingHom = ⊤ ∨
          RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f z c)).toRingHom ∈
            (⊥ : Ideal _).minimalPrimes) := by
  classical
  choose a b ha hb hm using fun w : {w : W // 2 ≤ rank w} => hhigh w.val w.property
  let J := ({w : W // 2 ≤ rank w} × C) ⊕ C
  let AJ : J → CommAlgCat.{u} S := fun j => A (j.elim (fun x => x.2) id)
  let BJ : J → CommAlgCat.{u} S := Sum.elim (fun x => B x.1.val x.2) (fun c => B z c)
  let fJ : ∀ j, AJ j →ₐ[S] BJ j := fun j => match j with
    | .inl x => f x.1.val x.2
    | .inr c => f z c
  let IJ : ∀ j, Ideal (AJ j) := fun j => match j with
    | .inl x => RingHom.ker (f (a x.1) x.2).toRingHom ⊔
        RingHom.ker (f (b x.1) x.2).toRingHom
    | .inr _ => ⊥
  have hfpAJ (j : J) : Algebra.FinitePresentation S (AJ j) :=
    hfpA (j.elim (fun x => x.2) id)
  have hfpBJ (j : J) : Algebra.FinitePresentation S (BJ j) := by
    cases j with
    | inl x => exact hfpB x.1.val x.2
    | inr c => exact hfpB z c
  have hsurjJ (j : J) : Function.Surjective (fJ j) := by
    cases j with
    | inl x => exact hsurj x.1.val x.2
    | inr c => exact hsurj z c
  have hcomponent (j : J) :
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (fJ j)).toRingHom = ⊤ ∨
      RingHom.ker (Algebra.TensorProduct.lTensor (S := K) K (fJ j)).toRingHom ∈
        ((IJ j).map (Algebra.TensorProduct.includeRight : AJ j →ₐ[S] K ⊗[S] AJ
          j).toRingHom).minimalPrimes := by
    cases j with
    | inl x => exact hm x.1 x.2
    | inr c =>
      dsimp only [AJ, BJ, fJ, IJ]
      rw [Ideal.map_bot]
      exact hzero c
  have witnessStage := @exists_minimalPrime_family_stage.{u}
    K hK S hS J inferInstance (fun j => AJ j) (fun j => BJ j)
    (fun j => (inferInstance : CommRing (AJ j)))
    (fun j => (inferInstance : Algebra S (AJ j))) hfpAJ
    (fun j => (inferInstance : CommRing (BJ j)))
    (fun j => (inferInstance : Algebra S (BJ j))) hfpBJ
    fJ hsurjJ IJ hcomponent
  obtain ⟨T, hST, hT, hfield⟩ := witnessStage
  refine ⟨T, hST, hT, ?_⟩
  intro L hL hTL
  let hSL : Algebra S L := ((algebraMap T L).comp
    (Subalgebra.inclusion hST).toRingHom).toAlgebra
  intro hp
  constructor
  · intro w hw
    refine ⟨a ⟨w, hw⟩, b ⟨w, hw⟩, ha ⟨w, hw⟩, hb ⟨w, hw⟩, ?_⟩
    intro c
    rcases @hfield L hL hTL (.inl (⟨w, hw⟩, c)) (hp w c) with htop | hmin
    · exact Or.inl htop
    · have hsum := @scalar_kernel_sup.{u} S L (A c)
        (B (a ⟨w, hw⟩) c) (B (b ⟨w, hw⟩) c)
        inferInstance inferInstance inferInstance
        inferInstance inferInstance hSL
        inferInstance inferInstance inferInstance
        (f (a ⟨w, hw⟩) c) (f (b ⟨w, hw⟩) c)
        (hsurj (a ⟨w, hw⟩) c) (hsurj (b ⟨w, hw⟩) c)
      change RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (f w c)).toRingHom ∈
        ((RingHom.ker (f (a ⟨w, hw⟩) c).toRingHom ⊔
          RingHom.ker (f (b ⟨w, hw⟩) c).toRingHom).map
          (Algebra.TensorProduct.includeRight :
            A c →ₐ[S] L ⊗[S] A c).toRingHom).minimalPrimes at hmin
      rw [hsum] at hmin
      exact Or.inr hmin
  · intro c
    have p := @hfield L hL hTL (.inr c) (hp z c)
    dsimp only [AJ, BJ, fJ, IJ] at p
    rw [Ideal.map_bot] at p
    exact p

open private tensor_spec_iso tensor_equifibered from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates
open private reindex_directed from
  OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets
open private scalar_arrow_cartesian from
  OrbitComplexity.SchubertGeometry.Connectedness.AppendCellConnected

/-- Scalar extension retains the quotient transformation's Cartesian diagram. -/
theorem quotient_tensor_equifibered
    (S R : Type u) [hS : CommRing S] [hR : CommRing R] [hSR : Algebra S R]
    {C : Type u} [hC : Category.{u} C] {I : Type u}
    (H : C ⥤ C) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
    (β : (Sigma.desc (fun _ : I => H)) ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ N) ⟶ Sum.inl_ (Σ _ : I, C) C ⋙
      N)
    (hcart : ∀ i, (Functor.whiskerRight
      (NatTrans.op (@quotient_component.{u} C hC I S hS H N β i))
      (algSpec (.of S) ⋙ scalar_functor
        (Spec.map (CommRingCat.ofHom (algebraMap S R))) ⋙ Over.forget _)).Equifibered) :
    let NR := N ⋙ tensor_functor S R
    let βR := Functor.whiskerRight β (tensor_functor S R)
    ∀ i, (Functor.whiskerRight
      (NatTrans.op (@quotient_component.{u} C hC I R hR H NR βR i))
      (algSpec (.of R) ⋙ Over.forget _)).Equifibered := by
  intro NR βR i a b f
  have producer := @tensor_equifibered.{u,u,u} S R hS hR hSR C hC
    (H ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ N)) (Sigma.incl (C := fun _ : I => C) i ⋙ (Sum.inl_ (Σ _ : I, C)
      C ⋙ N))
    (@quotient_component.{u} C hC I S hS H N β i)
  have h := producer (hcart i)
  exact @h a b f

/-- The scalar ambient diagram has open transition maps. -/
theorem ambient_tensor_open
    (S R : Type u) [hS : CommRing S] [hR : CommRing R] [hSR : Algebra S R]
    {C I : Type u} [hC : Category.{u} C]
    (H : C ⥤ C) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
    (hopen : ∀ x y (a : x ⟶ y),
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (N.map a).hom.toRingHom))) :
    ∀ {i j : Cᵒᵖ} (a : i ⟶ j),
      IsOpenImmersion
        ((((H ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ (N ⋙ tensor_functor S R))).op ⋙
          algSpec (.of R)).map a).left) := by
  intro i j a
  have h : IsOpenImmersion
      (((algSpec (.of S)).map
        (N.map ((Sum.inr_ (Σ _ : I, C) C).map (H.map a.unop))).op).left) :=
    hopen (.inr (H.obj j.unop)) (.inr (H.obj i.unop))
      ((Sum.inr_ (Σ _ : I, C) C).map (H.map a.unop))
  exact @tensor_open.{u} S R hS hR hSR
    (N.obj (.inr (H.obj j.unop))) (N.obj (.inr (H.obj i.unop)))
    (N.map ((Sum.inr_ (Σ _ : I, C) C).map (H.map a.unop))) h

/-- Pushout refinements make the scalar ambient diagram a directed atlas. -/
theorem ambient_tensor_directed
    (S R K : Type u) [hS : CommRing S] [hR : CommRing R] [hK : CommRing K]
    [hSR : Algebra S R] {C I : Type u} [hC : Category.{u} C]
    (H : C ⥤ C) (hH : H = 𝟭 C)
    (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
    (F : C ⥤ CommAlgCat.{u} K)
    (hretain : ∀ (i j k l : C) (a : i ⟶ j) (b : i ⟶ k) (p : j ⟶ l) (q : k ⟶ l),
      IsPushout (CommRingCat.ofHom (F.map a).hom.toRingHom)
        (CommRingCat.ofHom (F.map b).hom.toRingHom)
        (CommRingCat.ofHom (F.map p).hom.toRingHom)
        (CommRingCat.ofHom (F.map q).hom.toRingHom) →
      IsPushout
        (CommRingCat.ofHom (N.map ((Sum.inr_ (Σ _ : I, C) C).map a)).hom.toRingHom)
        (CommRingCat.ofHom (N.map ((Sum.inr_ (Σ _ : I, C) C).map b)).hom.toRingHom)
        (CommRingCat.ofHom (N.map ((Sum.inr_ (Σ _ : I, C) C).map p)).hom.toRingHom)
        (CommRingCat.ofHom (N.map ((Sum.inr_ (Σ _ : I, C) C).map q)).hom.toRingHom))
    (hrefine : ∀ (i j k : C) (a : k ⟶ i) (b : k ⟶ j),
      ∃ (l : C) (p : i ⟶ l) (q : j ⟶ l),
        IsPushout (CommRingCat.ofHom (F.map a).hom.toRingHom)
          (CommRingCat.ofHom (F.map b).hom.toRingHom)
          (CommRingCat.ofHom (F.map p).hom.toRingHom)
          (CommRingCat.ofHom (F.map q).hom.toRingHom)) :
    (((H ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ (N ⋙ tensor_functor S R))).op ⋙
      algSpec (.of R) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected := by
  have tensor_refinements := @retain_refinements C hC R K hR hK
    (Sum.inr_ (Σ _ : I, C) C ⋙ (N ⋙ tensor_functor S R)) F
    (fun i j k l a b p q h =>
      @tensor_pushout.{u} S R hS hR hSR
        (N.obj (.inr i)) (N.obj (.inr j)) (N.obj (.inr k)) (N.obj (.inr l))
        (N.map ((Sum.inr_ (Σ _ : I, C) C).map a))
        (N.map ((Sum.inr_ (Σ _ : I, C) C).map b))
        (N.map ((Sum.inr_ (Σ _ : I, C) C).map p))
        (N.map ((Sum.inr_ (Σ _ : I, C) C).map q))
        (hretain i j k l a b p q h)) hrefine
  exact @reindex_directed C hC R hR H hH
    (Sum.inr_ (Σ _ : I, C) C ⋙ (N ⋙ tensor_functor S R)) tensor_refinements

/-- The prescribed quotient cocones have Cartesian squares at every chart. -/
theorem quotient_cocone_chart
    (S : Type u) [CommRing S] {C : Type u} [Category.{u} C]
    [Quiver.IsThin C] [Small.{u} C]
    (F B : C ⥤ CommAlgCat.{u} S)
    [hopen : ∀ {i j : Cᵒᵖ} (a : i ⟶ j), IsOpenImmersion (((F.op ⋙ algSpec (.of S)).map a).left)]
    [hdir : (((F.op ⋙ algSpec (.of S)) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected]
    (β : F ⟶ B)
    (hβ : (Functor.whiskerRight (NatTrans.op β) (algSpec (.of S) ⋙ Over.forget _)).Equifibered)
    (cF : Cocone (F.op ⋙ algSpec (.of S))) (hcF : IsColimit cF)
    (cB : Cocone (B.op ⋙ algSpec (.of S))) (hcB : IsColimit cB)
    (j : cB.pt ⟶ cF.pt)
    (hlegs : ∀ s, (cB.ι.app s).left ≫ j.left =
      ((algSpec (.of S)).map (β.app s.unop).op).left ≫ (cF.ι.app s).left)
    (s : C) :
    IsPullback (Spec.map (CommRingCat.ofHom (β.app s).hom.toRingHom))
      (cB.ι.app (op s)).left (cF.ι.app (op s)).left j.left := by
  exact @isPullback_colimit_component.{u,u,u} Cᵒᵖ inferInstance inferInstance inferInstance
    (B.op ⋙ algSpec (.of S) ⋙ Over.forget _)
    (F.op ⋙ algSpec (.of S) ⋙ Over.forget _)
    (fun {_ _} a => hopen a) hdir
    (Functor.whiskerRight (NatTrans.op β) (algSpec (.of S) ⋙ Over.forget _)) hβ
    ((Over.forget _).mapCocone cB) ((Over.forget _).mapCocone cF)
    (isColimitOfPreserves (Over.forget _) hcB)
    (isColimitOfPreserves (Over.forget _) hcF) j.left hlegs (op s)

/-- The tensor atlas has exactly the scalar pullback of the prescribed cocone point. -/
def tensorCocone
    (S L : Type u) [CommRing S] [CommRing L] [Algebra S L]
    {C : Type u} [Category.{u} C] (D : C ⥤ CommAlgCat.{u} S)
    (c : Cocone (D.op ⋙ algSpec (.of S))) :
    Cocone ((D ⋙ tensor_functor S L).op ⋙ algSpec (.of L)) :=
  (Cocone.precompose (Functor.isoWhiskerLeft D.op (tensor_spec_iso S L)).hom).obj
    ((scalar_functor (Spec.map (CommRingCat.ofHom (algebraMap S L)))).mapCocone c)

/-- Scalar extension preserves each specified quotient chart square. -/
theorem scalar_quotient_chart
    (S L : Type u) [CommRing S] [CommRing L] [Algebra S L]
    {C : Type u} [Category.{u} C] (F B : C ⥤ CommAlgCat.{u} S) (β : F ⟶ B)
    (cF : Cocone (F.op ⋙ algSpec (.of S))) (cB : Cocone (B.op ⋙ algSpec (.of S)))
    (j : cB.pt ⟶ cF.pt) (s : C)
    (hcart : IsPullback ((algSpec (.of S)).map (β.app s).op).left
      (cB.ι.app (op s)).left (cF.ι.app (op s)).left j.left) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lTensor (S := L) L (β.app s).hom).toRingHom))
      ((tensorCocone S L B cB).ι.app (op s)).left
      ((tensorCocone S L F cF).ι.app (op s)).left
      ((scalar_functor (Spec.map (CommRingCat.ofHom (algebraMap S L)))).map j).left := by
  have hOver : IsPullback ((algSpec (.of S)).map (β.app s).op)
      (cB.ι.app (op s)) (cF.ι.app (op s)) j :=
    IsPullback.of_map_of_faithful (Over.forget _) hcart
  have hL := (hOver.map (scalar_functor
    (Spec.map (CommRingCat.ofHom (algebraMap S L))))).map (Over.forget _)
  exact hL.of_iso'
    ((Over.forget _).mapIso ((tensor_spec_iso S L).app (op (B.obj s))))
    ((Over.forget _).mapIso ((tensor_spec_iso S L).app (op (F.obj s))))
    (Iso.refl _) (Iso.refl _)
    (congrArg Over.Hom.left ((tensor_spec_iso S L).hom.naturality (β.app s).op)).symm
    (by simp only [Iso.refl_hom]; rfl)
    (by simp only [Iso.refl_hom]; rfl)
    (by exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- Pullback chart squares transport the covering property to their source. -/
private theorem cover_of_chart_pullbacks
    {X Y : Scheme.{u}} (U : X.OpenCover.{u}) (q : Y ⟶ X)
    (V : U.I₀ → Scheme.{u}) (k : ∀ i, V i ⟶ Y) (b : ∀ i, V i ⟶ U.X i)
    (hcart : ∀ i, IsPullback (k i) (b i) q (U.f i)) :
    ∀ y : Y, ∃ i z, k i z = y := by
  intro y
  let V : Y.OpenCover.{u} := U.pullback₁ q
  obtain ⟨i, z, hz⟩ := V.exists_eq y
  refine ⟨i, (hcart i).isoPullback.inv z, ?_⟩
  exact (congrArg (fun a => a z) (hcart i).isoPullback_inv_fst).trans hz

/-- A tensor chart is the inverse image of the original cocone chart. -/
private theorem scalar_cocone_chart
    (S L : Type u) [CommRing S] [CommRing L] [Algebra S L]
    {C : Type u} [Category.{u} C] (D : C ⥤ CommAlgCat.{u} S)
    (c : Cocone (D.op ⋙ algSpec (.of S))) (s : Cᵒᵖ) :
    IsPullback ((tensorCocone S L D c).ι.app s).left
      (((tensor_spec_iso S L).app (op (D.obj s.unop))).hom.left ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S L)))
          ((algSpec (.of S)).obj (op (D.obj s.unop))).hom)
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S L))) c.pt.hom)
      (c.ι.app s).left := by
  have h := scalar_arrow_cartesian
    (Spec.map (CommRingCat.ofHom (algebraMap S L))) (c.ι.app s)
  exact h.of_iso'
    ((Over.forget _).mapIso ((tensor_spec_iso S L).app (op (D.obj s.unop))))
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom]; rfl)
    (by simp only [Iso.refl_hom, Category.comp_id]; rfl)
    (by exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])

/-- The tensor charts cover exactly the scalar extension of the chosen cocone. -/
theorem tensor_cocone_cover
    (S L : Type u) [CommRing S] [CommRing L] [Algebra S L]
    {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    (D : C ⥤ CommAlgCat.{u} S)
    [hopen : ∀ {i j : Cᵒᵖ} (a : i ⟶ j), IsOpenImmersion (((D.op ⋙ algSpec (.of S)).map a).left)]
    [hdir : (((D.op ⋙ algSpec (.of S)) ⋙ Over.forget _) ⋙ Scheme.forget).IsLocallyDirected]
    (c : Cocone (D.op ⋙ algSpec (.of S))) (hc : IsColimit c) :
    (∀ s, IsOpenImmersion ((tensorCocone S L D c).ι.app s).left) ∧
      ∀ y : (tensorCocone S L D c).pt.left,
        ∃ s z, ((tensorCocone S L D c).ι.app s).left z = y := by
  let U := @coconeCover.{u} Cᵒᵖ inferInstance inferInstance
    (D.op ⋙ algSpec (.of S) ⋙ Over.forget _)
    (fun {_ _} a => hopen a) hdir
    ((Over.forget _).mapCocone c) (isColimitOfPreserves (Over.forget _) hc)
  have hcart (s : Cᵒᵖ) := scalar_cocone_chart S L D c s
  constructor
  · intro s
    have : IsOpenImmersion (U.f s) := U.map_prop s
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (hcart s).flip this
  · exact cover_of_chart_pullbacks U
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S L))) c.pt.hom)
      (fun s => ((D ⋙ tensor_functor S L).op ⋙ algSpec (.of L)).obj s |>.left)
      (fun s => ((tensorCocone S L D c).ι.app s).left)
      (fun s => ((tensor_spec_iso S L).app (op (D.obj s.unop))).hom.left ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S L)))
          ((algSpec (.of S)).obj (op (D.obj s.unop))).hom)
      hcart

end SchubertGeometry
