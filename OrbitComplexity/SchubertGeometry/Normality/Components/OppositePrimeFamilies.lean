import Mathlib.Tactic.DepRewrite
import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeScalarCoordinates
import OrbitComplexity.SchubertGeometry.Normality.Components.OppositeComponentCoordinates

/-! # Prime ideals on one affine atlas of opposite Schubert models -/

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

open private opposite_colimit_prime_stage from
  OrbitComplexity.SchubertGeometry.Normality.Components.OppositeChartPrimes
open private closed_target_stage from
  OrbitComplexity.SchubertGeometry.Normality.Components.OppositeCoordinateStages

open private component_stage from
  OrbitComplexity.SchubertGeometry.Normality.Components.OppositeScalarCoordinates

private theorem component_kernel_eq {C : Type u} [cCat : Category.{u} C]
    {I R L : Type u} [rComm : CommRing R] [lComm : CommRing L] [rLAlg : Algebra R L]
    (H : C ⥤ C) (N : (Σ _ : I, C) ⊕ C ⥤ CommAlgCat.{u} R)
    (β : Sigma.desc (fun _ : I => H) ⋙ (Sum.inr_ (Σ _ : I, C) C ⋙ N) ⟶
      Sum.inl_ (Σ _ : I, C) C ⋙ N)
    (i j : I) (hij : i = j) (c : C) :
    RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L
      ((@quotient_component.{u} C cCat I R rComm H N β i).app c).hom).toRingHom =
    RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (β.app ⟨j, c⟩).hom).toRingHom := by
  cases hij
  rfl

set_option maxHeartbeats 400000 in
/-- One family of opposite Schubert coordinate rings has prime or unit scalar kernels
on every affine intersection after one coefficient enlargement. Higher members retain
their minimal-prime relations to two lower members, and the identity member retains its
minimal-prime relation to zero. The flag and both scalar projections are retained. -/
theorem exists_opposite_prime_families
    {K T : Type u} [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    [hT : Finite T]
    (G : ReductiveGroups.ReductiveGroupData K)
    (U : T → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (hcover : (⨆ t, U t) = ⊤)
    (S₀ : Subalgebra ℤ K) (hS₀ : S₀.FG) (P : Over (Spec (.of S₀)))
    [hPCompact : CompactSpace P.left] [hPFP : LocallyOfFinitePresentation P.hom]
    (qP : (flagVariety G).scheme ⟶ P.left)
    (hP : IsPullback qP (flagVariety G).toSpec P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
    (start : CoefficientStage S₀) :
    let C := {s : Finset T // s.Nonempty}
    ∃ selected : @ClosedCoordinateStage K T G.weylGroup hK hAlg hChar
        G (oppositeSchubertSupport G) U hU S₀ P qP start,
      let _ : Algebra selected.S selected.k.val :=
        (Subalgebra.inclusion selected.k.property.2).toAlgebra
      let _ : IsScalarTower selected.S selected.k.val K :=
        Subalgebra.inclusion.isScalarTower_right selected.k.property.2 K
      let Nₖ := selected.N ⋙ tensor_functor selected.S selected.k.val
      let βₖ := Functor.whiskerRight selected.β (tensor_functor selected.S selected.k.val)
      ∃ R : CoefficientStage selected.k.val,
        @componentKernelStage.{u} K G.weylGroup C hK.toCommRing inferInstance
          selected.k.val (intersectionIndexMap (id : T → T)) Nₖ βₖ
          (weylCoxeterSystem G.rootBase).length 1 R := by
  classical
  intro C
  let j := fun i => (flagVariety G).closedInclusion (oppositeSchubertSupport G i)
  have hWeyl : Finite G.weylGroup := weylGroup_finite G.rootBase
  have coordinates := @closed_target_stage K T G.weylGroup hK hAlg hChar hT hWeyl
    G (oppositeSchubertSupport G) U hU hcover S₀ hS₀ P hPCompact hPFP qP hP start
  obtain ⟨selected⟩ := coordinates
  have components := @opposite_component_kernels.{u} K T hK hAlg hChar G U hU
    S₀ P qP start selected
  refine ⟨selected, ?_⟩
  rcases selected with ⟨S, hS, hS₀S, hstartS, N, e, β, hfp, hn, hβ, hsurj, hopen, hpush,
    qPS, hPS, hfirst, hsecond, k, htargets, hsurjK, hcartK, scalarProperties⟩
  intro hSk hSkK Nₖ βₖ
  have properties := scalarProperties
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let some decl := (← Lean.getLCtx).findFromUserName? `properties |
      throwError "missing coordinate properties"
    let typ ← Lean.Meta.whnf (← Lean.instantiateMVars decl.type)
    let typ ← Lean.Core.betaReduce typ
    let goal ← goal.replaceLocalDeclDefEq decl.fvarId typ
    Lean.Elab.Tactic.replaceMainGoal [goal]
  obtain ⟨hfpK, hnK, hβK, hsurjβK, hopenK, hdirK⟩ := properties
  let H₀ := intersectionIndexMap (id : T → T)
  let F₀ := H₀ ⋙ (Sum.inr_ (Σ _ : G.weylGroup, C) C ⋙ Nₖ)
  let B₀ := fun i : G.weylGroup =>
    Sigma.incl i ⋙ (Sum.inl_ (Σ _ : G.weylGroup, C) C ⋙ Nₖ)
  have targets := htargets
  obtain ⟨_qPk, _hPk, _hnF, _hnB, _hPkfirst, _hPksecond, _hOriginal,
    models, _flatten⟩ := targets
  obtain ⟨_cFM, cBM, _qF, qB, _jM, _hcFM, hcBM, _hclosed, _hqF, hqB,
    _hlegsF, _hlegsB, _hlegsβ, _htriangle, _later⟩ := models
  have hfpB (i : G.weylGroup) (c : C) :
      Algebra.FinitePresentation k.val ((B₀ i).obj c) := hfpK (.inl ⟨i, c⟩)
  have hopenB (i : G.weylGroup) {c d : C} (a : c ⟶ d) : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((B₀ i).map a).hom.toRingHom)) :=
    hopenK (.inl ⟨i, c⟩) (.inl ⟨i, d⟩)
      ((Sum.inl_ (Σ _ : G.weylGroup, C) C).map
        ((Sigma.incl (C := fun _ : G.weylGroup => C) i).map a))
  have hdirB (i : G.weylGroup) :
      (((B₀ i).op ⋙ algSpec (.of k.val) ⋙ Over.forget _) ⋙
        Scheme.forget).IsLocallyDirected :=
    hdirK i (@intersectionCoordinates_refine
        ((flagVariety G).closedSubvariety (oppositeSchubertSupport G i)).scheme T K
        hK.toCommRing
        (@variety_diagonal K hK
          ((flagVariety G).closedSubvariety (oppositeSchubertSupport G i)))
        ((j i).left ≫ (flagVariety G).toSpec) (fun t => (j i).left ⁻¹ᵁ U t)
        (fun t => (hU t).preimage (j i).left))
  obtain ⟨componentHigh, componentZero⟩ := components
  have quotient_surjective (w : G.weylGroup) (c : C) :
      Function.Surjective (((@quotient_component.{u} C inferInstance G.weylGroup k.val inferInstance
        (intersectionIndexMap (id : T → T)) Nₖ βₖ w).app c).hom) := hsurjβK ⟨w, c⟩
  have componentData := @component_stage.{u}
    K G.weylGroup C hK hWeyl inferInstance
    k.val k.property.1
    (fun c => Nₖ.obj (.inr ((intersectionIndexMap (id : T → T)).obj c)))
    (fun w c => Nₖ.obj (.inl ⟨w, c⟩))
    (fun w c => ((@quotient_component.{u} C inferInstance G.weylGroup k.val inferInstance
      (intersectionIndexMap (id : T → T)) Nₖ βₖ w).app c).hom)
    (fun c => hfpK (.inr ((intersectionIndexMap (id : T → T)).obj c)))
    (fun w c => hfpK (.inl ⟨w, c⟩)) quotient_surjective
    (weylCoxeterSystem G.rootBase).length 1 componentHigh componentZero
  obtain ⟨Scomp, hkScomp, hScomp, hComponents⟩ := componentData
  have primeData := @opposite_colimit_prime_stage K C G.weylGroup hK hAlg hChar
    inferInstance (inferInstance : Quiver.IsThin C)
    (inferInstance : Finite C) hWeyl G
    (fun w => chosenReducedWord G.rootBase (G.longestElement⁻¹ * w))
    (fun w => chosenReducedWord_isReduced G.rootBase (G.longestElement⁻¹ * w))
    k.val k.property.1 F₀
    (fun w => B₀ (G.longestElement * simpleWeylWord G.rootBase
      (chosenReducedWord G.rootBase (G.longestElement⁻¹ * w))))
    (fun w => quotient_component H₀ Nₖ βₖ
      (G.longestElement * simpleWeylWord G.rootBase
        (chosenReducedWord G.rootBase (G.longestElement⁻¹ * w))))
    (fun w c => hfpB (G.longestElement * simpleWeylWord G.rootBase
      (chosenReducedWord G.rootBase (G.longestElement⁻¹ * w))) c)
    (fun w {c d} f => hopenB (G.longestElement * simpleWeylWord G.rootBase
      (chosenReducedWord G.rootBase (G.longestElement⁻¹ * w))) f)
    (fun w => hdirB (G.longestElement * simpleWeylWord G.rootBase
      (chosenReducedWord G.rootBase (G.longestElement⁻¹ * w))))
    (fun w => cBM (G.longestElement * simpleWeylWord G.rootBase
      (chosenReducedWord G.rootBase (G.longestElement⁻¹ * w))))
    (fun w => (hcBM (G.longestElement * simpleWeylWord G.rootBase
      (chosenReducedWord G.rootBase (G.longestElement⁻¹ * w)))).some)
    (fun w => qB (G.longestElement * simpleWeylWord G.rootBase
      (chosenReducedWord G.rootBase (G.longestElement⁻¹ * w))))
    (fun w => hqB (G.longestElement * simpleWeylWord G.rootBase
      (chosenReducedWord G.rootBase (G.longestElement⁻¹ * w))))
    ⟨Scomp, hScomp, hkScomp⟩
  obtain ⟨R, hScompR, hprime⟩ := primeData
  refine ⟨R, ?_⟩
  unfold componentKernelStage
  intro L hL hRL _hKL
  have prime_family : ∀ x : Σ _ : G.weylGroup, C,
      RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (βₖ.app x).hom).toRingHom = ⊤ ∨
      (RingHom.ker (Algebra.TensorProduct.lTensor (S := L) L (βₖ.app x).hom).toRingHom).IsPrime :=
        by
    intro x
    rcases x with ⟨w, c⟩
    have prime := @hprime L hL hRL w c
    have hindex : G.longestElement * simpleWeylWord G.rootBase
        (chosenReducedWord G.rootBase (G.longestElement⁻¹ * w)) = w :=
      (congrArg (fun z => G.longestElement * z)
        (simpleWeylWord_chosenReducedWord G.rootBase (G.longestElement⁻¹ * w))).trans
          (mul_inv_cancel_left G.longestElement w)
    have hkernel := @component_kernel_eq.{u} C
      inferInstance
      G.weylGroup k.val L (Subalgebra.toCommRing k.val) (@Field.toCommRing L hL) _hKL
      H₀ Nₖ βₖ (G.longestElement * simpleWeylWord G.rootBase
        (chosenReducedWord G.rootBase (G.longestElement⁻¹ * w))) w hindex c
    exact Eq.mp (congrArg (fun I : Ideal _ => I = ⊤ ∨ I.IsPrime) hkernel) prime
  let algCompL : Algebra Scomp L := ((algebraMap R.val L).comp
    (Subalgebra.inclusion hScompR).toRingHom).toAlgebra
  have component_family := @hComponents L hL algCompL
  exact ⟨prime_family, component_family (fun w c => prime_family ⟨w, c⟩)⟩

end SchubertGeometry
