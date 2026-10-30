import OrbitComplexity.SchubertGeometry.Connectedness.PrefixStageCoordinates
import OrbitComplexity.SchubertGeometry.Connectedness.PrefixClosedTargets

set_option autoImplicit false

/-! # Common coefficients for closed Schubert targets

The finite quotient diagram and a specified flag model are extended to one
coefficient ring containing their coefficient rings. The extended diagram
constructs the closed targets, and the flag comparison retains its two
projections through all subsequent scalar extensions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ReductiveGroups
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry

universe u

open private scalar_functor
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendCellConnected
open private tensor_functor tensor_map_hom tensor_comparison tensor_comparison_natural
  tensor_comparison_original tensor_surjective_later tensor_open tensor_pushout
  scalar_flag scalar_tower_eq coefficient_triangle
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates
open private coefficient_targets
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixStageCoordinates
open private stage_properties
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing
open private variety_diagonal
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets

private theorem bind_four {A : Sort*} {B : A → Sort*} {C : ∀ a, B a → Sort*}
    {D : ∀ a b, C a b → Sort*} {P : ∀ a b c, D a b c → Prop} {Q : Prop}
    (h : ∃ a b c d, P a b c d) (f : ∀ a b c d, P a b c d → Q) : Q := by
  obtain ⟨a, b, c, d, hd⟩ := h
  exact f a b c d hd

private theorem bind_two {A : Sort*} {B : A → Sort*} {P : ∀ a, B a → Prop} {Q : Prop}
    (h : ∃ a b, P a b) (f : ∀ a b, P a b → Q) : Q := by
  obtain ⟨a, b, hab⟩ := h
  exact f a b hab

private theorem bind_one {A : Sort*} {P : A → Prop} {Q : Prop}
    (h : ∃ a, P a) (f : ∀ a, P a → Q) : Q := by
  obtain ⟨a, ha⟩ := h
  exact f a ha

private theorem tensor_surjective {R : Type u} [CommRing R]
    {M N : CommAlgCat.{u} R} (f : M ⟶ N) (h : Function.Surjective f.hom) :
    Function.Surjective (Algebra.TensorProduct.lTensor (S := R) R f.hom) :=
  Algebra.TensorProduct.map_surjective (AlgHom.id R R) f.hom (fun x => ⟨x, rfl⟩) h

private theorem extend_primitives {S R K : Type u}
    [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra S K] [Algebra R K] [IsScalarTower S R K]
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (U V : D ⥤ C) (N : C ⥤ CommAlgCat.{u} S) (A : C ⥤ CommAlgCat.{u} K)
    (e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K] A.obj x)
    (β : U ⋙ N ⟶ V ⋙ N) (δ : U ⋙ A ⟶ V ⋙ A)
    (hfp : ∀ x, Algebra.FinitePresentation S (N.obj x))
    (hn : ∀ x y (a : x ⟶ y), (e y).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (N.map a).hom) =
      (A.map a).hom.comp (e x).toAlgHom)
    (hβ : ∀ x, (e (V.obj x)).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (β.app x).hom) =
      (δ.app x).hom.comp (e (U.obj x)).toAlgHom)
    (hsurj : ∀ x, Function.Surjective
      (Algebra.TensorProduct.lTensor (S := R) R (β.app x).hom))
    (hopen : ∀ x y (a : x ⟶ y), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map a).hom.toRingHom)))
    (hpush : ∀ (x y z t) (a : x ⟶ y) (b : x ⟶ z) (p : y ⟶ t) (q : z ⟶ t),
      IsPushout (CommRingCat.ofHom (A.map a).hom.toRingHom)
        (CommRingCat.ofHom (A.map b).hom.toRingHom)
        (CommRingCat.ofHom (A.map p).hom.toRingHom)
        (CommRingCat.ofHom (A.map q).hom.toRingHom) →
      IsPushout (CommRingCat.ofHom (N.map a).hom.toRingHom)
        (CommRingCat.ofHom (N.map b).hom.toRingHom)
        (CommRingCat.ofHom (N.map p).hom.toRingHom)
        (CommRingCat.ofHom (N.map q).hom.toRingHom)) :
    let NR := N ⋙ tensor_functor S R
    let βR := Functor.whiskerRight β (tensor_functor S R)
    let eR := fun x => tensor_comparison S R (N.obj x) (A.obj x) (e x)
    (∀ x, Algebra.FinitePresentation R (NR.obj x)) ∧
    (∀ x y (a : x ⟶ y), (eR y).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (NR.map a).hom) =
      (A.map a).hom.comp (eR x).toAlgHom) ∧
    (∀ x, (eR (V.obj x)).toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := K) K (βR.app x).hom) =
      (δ.app x).hom.comp (eR (U.obj x)).toAlgHom) ∧
    (∀ x, Function.Surjective (βR.app x).hom) ∧
    (∀ x y (a : x ⟶ y), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (NR.map a).hom.toRingHom))) ∧
    ∀ (x y z t) (a : x ⟶ y) (b : x ⟶ z) (p : y ⟶ t) (q : z ⟶ t),
      IsPushout (CommRingCat.ofHom (A.map a).hom.toRingHom)
        (CommRingCat.ofHom (A.map b).hom.toRingHom)
        (CommRingCat.ofHom (A.map p).hom.toRingHom)
        (CommRingCat.ofHom (A.map q).hom.toRingHom) →
      IsPushout (CommRingCat.ofHom (NR.map a).hom.toRingHom)
        (CommRingCat.ofHom (NR.map b).hom.toRingHom)
        (CommRingCat.ofHom (NR.map p).hom.toRingHom)
        (CommRingCat.ofHom (NR.map q).hom.toRingHom) := by
  let : ∀ x, Algebra.FinitePresentation S (N.obj x) := hfp
  refine ⟨(fun x => inferInstanceAs (Algebra.FinitePresentation R (R ⊗[S] N.obj x))),
    (fun x y a => tensor_comparison_natural S R (e x) (e y) (N.map a) (A.map a) (hn x y a)),
    (fun x => tensor_comparison_natural S R _ _ (β.app x) (δ.app x) (hβ x)),
    ?_, ?_, ?_⟩
  · intro x
    change Function.Surjective (((tensor_functor S R).map (β.app x)).hom)
    rw [tensor_map_hom]
    exact hsurj x
  · intro x y a
    let : IsOpenImmersion ((algSpec (.of S)).map (N.map a).op).left := hopen x y a
    exact tensor_open S R (N.map a)
  · intro x y z t a b p q h
    exact tensor_pushout S R (N.map a) (N.map b) (N.map p) (N.map q)
      (hpush x y z t a b p q h)

private def common_targets
    {Y : Scheme.{u}} {J I K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (X : I → Scheme.{u}) [∀ i, IsAffineHom (pullback.diagonal (terminal.from (X i)))]
    (j : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (j i)]
    (base : Y ⟶ Spec (.of K)) (U : J → Y.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (S₀ : Subalgebra ℤ K) (P : Over (Spec (.of S₀))) (qF : Y ⟶ P.left)
    (start₀ : CoefficientStage S₀) : Prop :=
  let C := {s : Finset J // s.Nonempty}
  let H : (Σ _ : I, C) ⥤ C := Sigma.desc (fun _ => intersectionIndexMap (id : J → J))
  let A := (Sigma.desc (fun i => intersectionCoordinates (j i ≫ base)
    (intersectionOpens (fun t => j i ⁻¹ᵁ U t)))).sum' (intersectionCoordinates base
      (intersectionOpens U))
  ∃ (S : Subalgebra ℤ K) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
    (e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K] A.obj x)
    (β : H ⋙ (Sum.inr_ _ _ ⋙ N) ⟶ Sum.inl_ _ _ ⋙ N)
    (T : Subalgebra ℤ K) (h₀ : S₀ ≤ T) (h : S ≤ T),
    start₀.val ≤ T ∧ T.FG ∧
    let _ : Algebra S T := (Subalgebra.inclusion h).toAlgebra
    let _ : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right h K
    let _ : Algebra S₀ T := (Subalgebra.inclusion h₀).toAlgebra
    let _ : IsScalarTower S₀ T K := Subalgebra.inclusion.isScalarTower_right h₀ K
    let NT := N ⋙ tensor_functor S T
    let βT := Functor.whiskerRight β (tensor_functor S T)
    let eT := fun x => tensor_comparison S T (N.obj x) (A.obj x) (e x)
    let κ₀ := Spec.map (CommRingCat.ofHom (algebraMap S₀ T))
    let PT := (scalar_functor κ₀).obj P
    ∃ (qT : Y ⟶ PT.left)
      (_ : IsPullback qT base PT.hom
        (Spec.map (CommRingCat.ofHom (algebraMap T K)))),
      (qT ≫ pullback.fst κ₀ P.hom =
        base ≫ Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
      (qT ≫ pullback.snd κ₀ P.hom = qF) ∧
      (∀ x (z : N.obj x), eT x ((1 : K) ⊗ₜ[T] ((1 : T) ⊗ₜ[S] z)) =
        e x ((1 : K) ⊗ₜ[S] z)) ∧
      (∃ k : CoefficientStage T,
        coefficient_targets X j base U hU T NT eT βT PT qT k) ∧
      ∀ (L : Type u) [CommRing L] [Algebra S₀ L] [Algebra T L]
        [IsScalarTower S₀ T L],
        let τ := Spec.map (CommRingCat.ofHom (algebraMap T L))
        let ζ := Spec.map (CommRingCat.ofHom (algebraMap S₀ L))
        ∃ E : (scalar_functor τ).obj PT ≅ (scalar_functor ζ).obj P,
          E.hom.left ≫ pullback.fst ζ P.hom = pullback.fst τ PT.hom ∧
          E.hom.left ≫ pullback.snd ζ P.hom =
            pullback.snd τ PT.hom ≫ pullback.snd κ₀ P.hom

private theorem common_from_diagram
    {Y : Scheme.{u}} {J I K : Type u} [CommRing K] [Finite J] [Finite I]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (X : I → Scheme.{u}) [∀ i, IsAffineHom (pullback.diagonal (terminal.from (X i)))]
    (j : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (j i)]
    (base : Y ⟶ Spec (.of K)) (U : J → Y.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (hcover : (⨆ t, U t) = ⊤)
    (S₀ : Subalgebra ℤ K) (hS₀ : S₀.FG) (P : Over (Spec (.of S₀)))
    [CompactSpace P.left] [LocallyOfFinitePresentation P.hom]
    (qF : Y ⟶ P.left)
    (hF : IsPullback qF base P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
    (start₀ : CoefficientStage S₀) :
    let C := {s : Finset J // s.Nonempty}
    let H : (Σ _ : I, C) ⥤ C := Sigma.desc (fun _ => intersectionIndexMap (id : J → J))
    let A := (Sigma.desc (fun i => intersectionCoordinates (j i ≫ base)
      (intersectionOpens (fun t => j i ⁻¹ᵁ U t)))).sum' (intersectionCoordinates base
        (intersectionOpens U))
    ∀ (S : Subalgebra ℤ K) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} S)
      (e : ∀ x, K ⊗[S] N.obj x ≃ₐ[K] A.obj x)
      (β : H ⋙ (Sum.inr_ _ _ ⋙ N) ⟶ Sum.inl_ _ _ ⋙ N),
      (∀ x, Algebra.FinitePresentation S (N.obj x)) →
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
      ∀ (R : Subalgebra ℤ K) (hSR : S ≤ R),
        let _ : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
        R.FG → (∀ x, Function.Surjective
          (Algebra.TensorProduct.lTensor (S := R) R (β.app x).hom)) →
        common_targets X j base U hU S₀ P qF start₀ := by
  dsimp only
  intro S N e β hfp hn hβ hopen hpush R hSR
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  intro hR hsurj
  let T : Subalgebra ℤ K := start₀.val ⊔ R
  have hTfg : T.FG := start₀.property.1.sup hR
  have h₀ : S₀ ≤ T := start₀.property.2.trans le_sup_left
  have h : S ≤ T := hSR.trans le_sup_right
  let : Algebra S T := (Subalgebra.inclusion h).toAlgebra
  let : Algebra R T := (Subalgebra.inclusion le_sup_right).toAlgebra
  let : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right h K
  let : Algebra S₀ T := (Subalgebra.inclusion h₀).toAlgebra
  let : IsScalarTower S₀ T K := Subalgebra.inclusion.isScalarTower_right h₀ K
  let C := {s : Finset J // s.Nonempty}
  let H : (Σ _ : I, C) ⥤ C := Sigma.desc (fun _ => intersectionIndexMap (id : J → J))
  let A := (Sigma.desc (fun i => intersectionCoordinates (j i ≫ base)
    (intersectionOpens (fun t => j i ⁻¹ᵁ U t)))).sum' (intersectionCoordinates base
      (intersectionOpens U))
  let δ : H ⋙ (Sum.inr_ _ _ ⋙ A) ⟶ Sum.inl_ _ _ ⋙ A :=
    Sigma.natTrans (C := fun _ : I => C) (fun i => intersectionCoordinateMap (j i) base
      (fun t => j i ⁻¹ᵁ U t) U id (fun _ => le_rfl))
  let NT : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} T := N ⋙ tensor_functor S T
  let βT : H ⋙ (Sum.inr_ _ _ ⋙ NT) ⟶ Sum.inl_ _ _ ⋙ NT :=
    Functor.whiskerRight β (tensor_functor S T)
  let eT : ∀ x, K ⊗[T] NT.obj x ≃ₐ[K] A.obj x :=
    fun x => tensor_comparison S T (N.obj x) (A.obj x) (e x)
  have hsurjT : ∀ x, Function.Surjective
      (Algebra.TensorProduct.lTensor (S := T) T (β.app x).hom) :=
    fun x => tensor_surjective_later S R (K := T) (β.app x) (hsurj x)
  have hprops := extend_primitives (S := S) (R := T) (K := K)
    (H ⋙ Sum.inr_ _ _) (Sum.inl_ _ _) N A e β δ
    hfp hn hβ hsurjT hopen hpush
  let κ₀ := Spec.map (CommRingCat.ofHom (algebraMap S₀ T))
  let PT : Over (Spec (.of T)) := (scalar_functor κ₀).obj P
  have hPprops := stage_properties S₀ hS₀ P ⟨T, hTfg, h₀⟩
  let : CompactSpace PT.left := hPprops.2.1
  let : QuasiSeparatedSpace PT.left := hPprops.2.2
  let : LocallyOfFinitePresentation PT.hom := hPprops.1
  apply bind_one (scalar_flag S₀ T P (Over.mk base) qF hF)
  intro qT hqT
  have hstage := exists_prefix_stage_coordinates X j base U hU hcover T NT eT βT
    hTfg hprops.1 hprops.2.1 hprops.2.2.1 hprops.2.2.2.2.1 hprops.2.2.2.2.2
    ⟨T, hTfg, le_rfl⟩
    (fun x => tensor_surjective (R := T) (βT.app x) (hprops.2.2.2.1 x)) PT qT hqT.1
  have hstage' : ∃ k : CoefficientStage T,
      coefficient_targets X j base U hU T NT eT βT PT qT k := by
    exact bind_one hstage (fun k hk => ⟨k, hk.2⟩)
  refine ⟨S, N, e, β, T, h₀, h, le_sup_left, hTfg, qT, hqT.1,
    hqT.2.1, hqT.2.2, ?_, hstage', ?_⟩
  · exact fun x z => tensor_comparison_original S T (N.obj x) (A.obj x) (e x) 1 z
  · intro L _ _ _ _
    exact scalar_tower_eq κ₀ (Spec.map (CommRingCat.ofHom (algebraMap T L)))
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ L))) (coefficient_triangle S₀ T (K := L)) P

/-- The quotient atlas of a finite Schubert family constructs closed targets
over coefficients extending a specified flag model and a specified starting
stage. The flag comparison and all later scalar identifications retain both
projections to the specified model and coefficient base. -/
theorem exists_prefix_common_coefficients
    {K J I : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Finite J] [Finite I]
    (G : ReductiveGroupData K) (w : I → G.weylGroup)
    (U : J → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (hcover : (⨆ t, U t) = ⊤)
    (S₀ : Subalgebra ℤ K) (hS₀ : S₀.FG) (P : Over (Spec (.of S₀)))
    [CompactSpace P.left] [LocallyOfFinitePresentation P.hom]
    (qF : (flagVariety G).scheme ⟶ P.left)
    (hF : IsPullback qF (flagVariety G).toSpec P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
    (start₀ : CoefficientStage S₀) :
    let X := fun i => ((flagVariety G).closedSubvariety (schubertSupport G (w i))).scheme
    let j : ∀ i, X i ⟶ (flagVariety G).scheme :=
      fun i => ((flagVariety G).closedInclusion (schubertSupport G (w i))).left
    let _ : IsAffineHom (pullback.diagonal (terminal.from (flagVariety G).scheme)) :=
      variety_diagonal (flagVariety G)
    let _ (i : I) : IsAffineHom (pullback.diagonal (terminal.from (X i))) :=
      variety_diagonal ((flagVariety G).closedSubvariety (schubertSupport G (w i)))
    common_targets X j (flagVariety G).toSpec U hU S₀ P qF start₀ := by
  let X := fun i => ((flagVariety G).closedSubvariety (schubertSupport G (w i))).scheme
  let j : ∀ i, X i ⟶ (flagVariety G).scheme :=
    fun i => ((flagVariety G).closedInclusion (schubertSupport G (w i))).left
  let : IsAffineHom (pullback.diagonal (terminal.from (flagVariety G).scheme)) :=
    variety_diagonal (flagVariety G)
  let (i : I) : IsAffineHom (pullback.diagonal (terminal.from (X i))) :=
    variety_diagonal ((flagVariety G).closedSubvariety (schubertSupport G (w i)))
  apply bind_four (exists_prefix_chart_quotients G w U hU)
  intro S N e β h
  apply bind_two h.2
  intro R hSR hR
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  exact common_from_diagram X j (flagVariety G).toSpec U hU hcover S₀ hS₀ P qF hF start₀
    S N e β h.1.2.1 h.1.2.2.2.1 h.1.2.2.2.2.2.1
    h.1.2.2.2.2.2.2.2.1 h.1.2.2.2.2.2.2.2.2 R hSR hR.1 hR.2


end SchubertGeometry
