import OrbitComplexity.SchubertGeometry.Connectedness.CellGeometric
import OrbitComplexity.SchubertGeometry.Normality.Cells.CellProducts
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedIsomorphisms
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps
import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.CellModelMaps
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedMaps

/-! # Retaining the cell morphisms on a common coefficient stage -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace SchubertGeometry.CellContraction
universe u v
attribute [local instance] coefficientAlgebra

private theorem retained_comparison_square
    {T : Type*} [Category T] {S : T} {A B X Y : Over S} {A₀ B₀ : T}
    (e : A ≅ X) (d : Y ≅ B) (f : X ⟶ Y) {m : A ⟶ B}
    (hm : m = e.hom ≫ f ≫ d.hom)
    (qA : A.left ⟶ A₀) (qB : B.left ⟶ B₀) (f₀ : A₀ ⟶ B₀)
    (h : qA ≫ f₀ = m.left ≫ qB) :
    (e.inv.left ≫ qA) ≫ f₀ = f.left ≫ d.hom.left ≫ qB := by
  have hcancel : e.inv.left ≫ e.hom.left = 𝟙 X.left := by
    simpa only [Over.comp_left, Over.id_left] using congrArg Over.Hom.left e.inv_hom_id
  rw [hm, Over.comp_left, Over.comp_left] at h
  calc
    _ = e.inv.left ≫ (qA ≫ f₀) := Category.assoc _ _ _
    _ = e.inv.left ≫ ((e.hom.left ≫ f.left ≫ d.hom.left) ≫ qB) :=
      congrArg (fun k => e.inv.left ≫ k) h
    _ = _ := by simp only [← Category.assoc, hcancel, Category.id_comp]

private theorem exists_conjugated_models
    {K : Type u} [CommRing K] (R : Subalgebra ℤ K) (hR : R.FG)
    {I : Type v} [Fintype I] (X : I → Scheme.{u}) (D : Scheme.{u})
    [∀ i, CompactSpace (X i)] [∀ i, QuasiSeparatedSpace (X i)]
    (a : ∀ i, X i ⟶ Spec (.of R)) (d : D ⟶ Spec (.of R))
    [LocallyOfFinitePresentation d] (N : I → Over (Spec (.of K)))
    (Y : Over (Spec (.of K))) (e : ∀ i, FrobeniusSplitting.genericScalarModel R (a i) ≅ N i)
    (E : Y ≅ FrobeniusSplitting.genericScalarModel R d) (g : ∀ i, N i ⟶ Y)
    (m : ∀ i, FrobeniusSplitting.genericScalarModel R (a i) ⟶
      FrobeniusSplitting.genericScalarModel R d)
    (hm : ∀ i, m i = (e i).hom ≫ g i ≫ E.hom)
    (start : FrobeniusSplitting.CoefficientStage R) :
    ∃ (j : FrobeniusSplitting.CoefficientStage R) (_ : start ≤ j)
      (f : ∀ i, FrobeniusSplitting.stageScalarModel R (a i) j ⟶
        FrobeniusSplitting.stageScalarModel R d j), ∀ i,
      ((FrobeniusSplitting.modelScalarCone R (a i)).π.app (op j) ≫ (f i).left =
        (m i).left ≫ (FrobeniusSplitting.modelScalarCone R d).π.app (op j)) ∧
      (((e i).inv.left ≫ (FrobeniusSplitting.modelScalarCone R (a i)).π.app (op j)) ≫
        (f i).left = (g i).left ≫ E.hom.left ≫
          (FrobeniusSplitting.modelScalarCone R d).π.app (op j)) := by
  obtain ⟨j, hstart, f, hf⟩ := FrobeniusSplitting.exists_retained_maps R hR X
    (fun _ => D) a (fun _ => d) m start
  refine ⟨j, hstart, f, ?_⟩
  intro i
  exact ⟨hf i, retained_comparison_square (e i) E (g i) (hm i)
    _ _ (f i).left (hf i)⟩

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) {R : Subalgebra ℤ K}

/-- All specified arithmetic cell maps descend together above any prescribed
stage on the same chosen Richardson model. Both the generic square and the
square written with the original cell projections are retained. -/
theorem exists_cellArithmeticMaps (a b : G.weylGroup) (hR : R.FG)
    (M : ∀ w : {w : G.weylGroup // Nonempty (cellIntersection G a b w).left},
      FrobeniusSplitting.ArithmeticContractionModel (R := R)
        (cellContractionAlg G a b w.val) (cellOriginAlg G a b w.val w.property))
    {D : Scheme.{u}} (d : D ⟶ Spec (.of R)) [LocallyOfFinitePresentation d]
    (qD : (richardsonVariety G a b).scheme ⟶ D)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec d
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (start : FrobeniusSplitting.CoefficientStage R) :
    ∃ (j : FrobeniusSplitting.CoefficientStage R) (_ : start ≤ j)
      (f : ∀ w : {w : G.weylGroup // Nonempty (cellIntersection G a b w).left},
        FrobeniusSplitting.stageScalarModel R
          (cellArithmeticBase G a b w.val w.property (M w)) j ⟶
        FrobeniusSplitting.stageScalarModel R d j),
      ∀ w : {w : G.weylGroup // Nonempty (cellIntersection G a b w).left},
        ((FrobeniusSplitting.modelScalarCone R
          (cellArithmeticBase G a b w.val w.property (M w))).π.app (op j) ≫
            (f w).left =
          (cellArithmeticMap G a b w.val w.property (M w) d qD hD).left ≫
            (FrobeniusSplitting.modelScalarCone R d).π.app (op j)) ∧
        (((cellArithmeticGenericIso G a b w.val w.property (M w)).inv.left ≫
          (FrobeniusSplitting.modelScalarCone R
            (cellArithmeticBase G a b w.val w.property (M w))).π.app (op j)) ≫
            (f w).left =
          (pullback.snd (schubertCellInclusion G w.val)
            (richardsonInclusion G a b)).left ≫
            (chosenGenericIso R (richardsonVariety G a b).toOver d qD hD).hom.left ≫
              (FrobeniusSplitting.modelScalarCone R d).π.app (op j)) := by
  classical
  let : Finite G.weylGroup := ReductiveGroups.weylGroup_finite G.rootBase
  let I := {w : G.weylGroup // Nonempty (cellIntersection G a b w).left}
  let : Fintype I := Fintype.ofFinite I
  let (w : I) : CompactSpace (Spec (.of (M w).model)) := inferInstance
  let (w : I) : QuasiSeparatedSpace (Spec (.of (M w).model)) := inferInstance
  exact exists_conjugated_models R hR (fun w : I => Spec (.of (M w).model)) D
    (fun w => cellArithmeticBase G a b w.val w.property (M w)) d
    (fun w => cellIntersection G a b w.val) (richardsonVariety G a b).toOver
    (fun w => cellArithmeticGenericIso G a b w.val w.property (M w))
    (chosenGenericIso R (richardsonVariety G a b).toOver d qD hD)
    (fun w => pullback.snd (schubertCellInclusion G w.val) (richardsonInclusion G a b))
    (fun w => cellArithmeticMap G a b w.val w.property (M w) d qD hD)
    (fun _ => rfl) start

end SchubertGeometry.CellContraction


namespace SchubertGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting GroupActions Opposite CellContraction
open CartesianMonoidalCategory MonoidalCategory

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Over.cartesianMonoidalCategory

/-- A finite family of coefficient stages has a common upper bound. -/
theorem curveFamily_upper_stage {I J : Type*} [Fintype I] [Preorder J]
    [IsDirectedOrder J] (k : I → J) (start : J) :
    ∃ l, start ≤ l ∧ ∀ r, k r ≤ l := by
  classical
  have aux : ∀ s : Finset I, ∃ l, start ≤ l ∧ ∀ r ∈ s, k r ≤ l := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨start, le_rfl, by simp⟩
    | @insert r s _ ih =>
      obtain ⟨l, hl, hs⟩ := ih
      obtain ⟨m, hlm, hrm⟩ := exists_ge_ge l (k r)
      refine ⟨m, hl.trans hlm, ?_⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with htr | hts
      · exact htr.symm ▸ hrm
      · exact (hs t hts).trans hlm
  obtain ⟨l, hl, hs⟩ := aux Finset.univ
  exact ⟨l, hl, fun r => hs r (Finset.mem_univ r)⟩

private theorem extend_identity {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j) :
    extendModelMorphism S a a hij (𝟙 (stageScalarModel S a i)) =
      𝟙 (stageScalarModel S a j) := by
  apply (Over.forget (Spec (.of j.val))).map_injective
  change (extendModelMorphism S a a hij (𝟙 _)).left = 𝟙 _
  apply (stageScalarCartesian S a hij).hom_ext
  · simpa only [Over.id_left, Category.comp_id, Category.id_comp] using
      extendModelMorphism_transition S a a hij (𝟙 (stageScalarModel S a i))
  · exact (extendModelMorphism S a a hij (𝟙 _)).w.trans (Category.id_comp _).symm

/-- Extending specified morphisms to a later stage preserves composition. -/
theorem curveModel_extend_composition {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X Y Z : Scheme.{u}} (a : X ⟶ Spec (.of S))
    (b : Y ⟶ Spec (.of S)) (c : Z ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i)
    (g : stageScalarModel S b i ⟶ stageScalarModel S c i) :
    extendModelMorphism S a c hij (f ≫ g) =
      extendModelMorphism S a b hij f ≫ extendModelMorphism S b c hij g := by
  apply (Over.forget (Spec (.of j.val))).map_injective
  change (extendModelMorphism S a c hij (f ≫ g)).left =
    (extendModelMorphism S a b hij f).left ≫ (extendModelMorphism S b c hij g).left
  apply (stageScalarCartesian S c hij).hom_ext
  · calc
      (extendModelMorphism S a c hij (f ≫ g)).left ≫ stageScalarTransition S c hij =
          stageScalarTransition S a hij ≫ (f.left ≫ g.left) :=
        extendModelMorphism_transition S a c hij (f ≫ g)
      _ = (stageScalarTransition S a hij ≫ f.left) ≫ g.left :=
        (Category.assoc _ _ _).symm
      _ = ((extendModelMorphism S a b hij f).left ≫
          stageScalarTransition S b hij) ≫ g.left :=
        congrArg (fun k => k ≫ g.left) (extendModelMorphism_transition S a b hij f).symm
      _ = (extendModelMorphism S a b hij f).left ≫
          (stageScalarTransition S b hij ≫ g.left) := Category.assoc _ _ _
      _ = (extendModelMorphism S a b hij f).left ≫
          ((extendModelMorphism S b c hij g).left ≫ stageScalarTransition S c hij) :=
        congrArg (fun k => (extendModelMorphism S a b hij f).left ≫ k)
          (extendModelMorphism_transition S b c hij g).symm
      _ = ((extendModelMorphism S a b hij f).left ≫
          (extendModelMorphism S b c hij g).left) ≫ stageScalarTransition S c hij :=
        (Category.assoc _ _ _).symm
  · exact (extendModelMorphism S a c hij (f ≫ g)).w.trans
      (extendModelMorphism S a b hij f ≫ extendModelMorphism S b c hij g).w.symm

/-- The scalar extension of a specified isomorphism to a later coefficient stage. -/
def curveFamilyExtendIso {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X Y : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    {i j : CoefficientStage S} (hij : i ≤ j)
    (E : stageScalarModel S a i ≅ stageScalarModel S b i) :
    stageScalarModel S a j ≅ stageScalarModel S b j where
  hom := extendModelMorphism S a b hij E.hom
  inv := extendModelMorphism S b a hij E.inv
  hom_inv_id := by
    calc
      extendModelMorphism S a b hij E.hom ≫ extendModelMorphism S b a hij E.inv =
          extendModelMorphism S a a hij (E.hom ≫ E.inv) :=
        (curveModel_extend_composition S a b a hij E.hom E.inv).symm
      _ = extendModelMorphism S a a hij (𝟙 _) :=
        congrArg (extendModelMorphism S a a hij) E.hom_inv_id
      _ = 𝟙 _ := extend_identity S a hij
  inv_hom_id := by
    calc
      extendModelMorphism S b a hij E.inv ≫ extendModelMorphism S a b hij E.hom =
          extendModelMorphism S b b hij (E.inv ≫ E.hom) :=
        (curveModel_extend_composition S b a b hij E.inv E.hom).symm
      _ = extendModelMorphism S b b hij (𝟙 _) :=
        congrArg (extendModelMorphism S b b hij) E.inv_hom_id
      _ = 𝟙 _ := extend_identity S b hij

private theorem natural_triangle {T : Type*} [Category T]
    {C D B Ci Di Bi Cj Dj Bj : T}
    (pCi : Ci ⟶ C) (pDi : Di ⟶ D) (bCi : Ci ⟶ Bi) (bDi : Di ⟶ Bi)
    (d : D ⟶ B) (κ : Bi ⟶ B) (hDi : IsPullback pDi bDi d κ)
    (pCj : Cj ⟶ C) (pDj : Dj ⟶ D) (bCj : Cj ⟶ Bj) (bDj : Dj ⟶ Bj)
    (tC : Cj ⟶ Ci) (tD : Dj ⟶ Di) (μ : Bj ⟶ Bi)
    (f : C ⟶ D) (fi : Ci ⟶ Di) (fj : Cj ⟶ Dj)
    (hi : fi ≫ pDi = pCi ≫ f) (hj : fj ≫ pDj = pCj ≫ f)
    (hCi : fi ≫ bDi = bCi) (hCj : fj ≫ bDj = bCj)
    (hCt : tC ≫ pCi = pCj) (hDt : tD ≫ pDi = pDj)
    (hCb : tC ≫ bCi = bCj ≫ μ) (hDb : tD ≫ bDi = bDj ≫ μ) :
    fj ≫ tD = tC ≫ fi := by
  apply hDi.hom_ext
  · calc
      (fj ≫ tD) ≫ pDi = fj ≫ pDj :=
        (Category.assoc _ _ _).trans (congrArg (fun k => fj ≫ k) hDt)
      _ = pCj ≫ f := hj
      _ = (tC ≫ pCi) ≫ f := congrArg (fun k => k ≫ f) hCt.symm
      _ = tC ≫ (fi ≫ pDi) :=
        (Category.assoc _ _ _).trans (congrArg (fun k => tC ≫ k) hi.symm)
      _ = (tC ≫ fi) ≫ pDi := (Category.assoc _ _ _).symm
  · calc
      (fj ≫ tD) ≫ bDi = fj ≫ (bDj ≫ μ) :=
        (Category.assoc _ _ _).trans (congrArg (fun k => fj ≫ k) hDb)
      _ = (fj ≫ bDj) ≫ μ := (Category.assoc _ _ _).symm
      _ = bCj ≫ μ := congrArg (fun k => k ≫ μ) hCj
      _ = tC ≫ bCi := hCb.symm
      _ = tC ≫ (fi ≫ bDi) := congrArg (fun k => tC ≫ k) hCi.symm
      _ = (tC ≫ fi) ≫ bDi := (Category.assoc _ _ _).symm

/-- Extending a scalar comparison preserves its specified naturality square. -/
theorem curveModel_extend_arrow {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {C D : Over (Spec (.of S))} (f : C ⟶ D)
    {i j : CoefficientStage S} (hij : i ≤ j) :
    extendModelMorphism S C.hom D.hom hij
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)) f) =
      chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)) f := by
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let κj := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let fi := chosenScalarArrow κi f
  let fj := chosenScalarArrow κj f
  have hn : fj.left ≫ stageScalarTransition S D.hom hij =
      stageScalarTransition S C.hom hij ≫ fi.left :=
    natural_triangle (pullback.snd κi C.hom) (pullback.snd κi D.hom)
      (stageScalarModel S C.hom i).hom (stageScalarModel S D.hom i).hom D.hom κi
      (IsPullback.of_hasPullback κi D.hom).flip
      (pullback.snd κj C.hom) (pullback.snd κj D.hom)
      (stageScalarModel S C.hom j).hom (stageScalarModel S D.hom j).hom
      (stageScalarTransition S C.hom hij) (stageScalarTransition S D.hom hij)
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hij).toRingHom))
      f.left fi.left fj.left (chosenScalarArrow_snd κi f) (chosenScalarArrow_snd κj f)
      fi.w fj.w (stageScalarTransition_snd S C.hom hij)
      (stageScalarTransition_snd S D.hom hij)
      (stageScalarTransition_fst S C.hom hij) (stageScalarTransition_fst S D.hom hij)
  apply (Over.forget (Spec (.of j.val))).map_injective
  change (extendModelMorphism S C.hom D.hom hij fi).left = fj.left
  apply (stageScalarCartesian S D.hom hij).hom_ext
  · exact (extendModelMorphism_transition S C.hom D.hom hij fi).trans hn.symm
  · exact (extendModelMorphism S C.hom D.hom hij fi).w.trans fj.w.symm

/-- Connected coefficient-stage fibres for a finite family of curve intersections. -/
def familyCurveResult
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} {I IK : J → Scheme.{u}}
    (b : ∀ r, I r ⟶ Spec (.of S)) (bK : ∀ r, IK r ⟶ Spec (.of K))
    (qI : ∀ r, IK r ⟶ I r) (start : CoefficientStage S) : Prop :=
  ∃ (k : CoefficientStage S) (_ : start ≤ k)
    (qK : ∀ r, IK r ⟶ (stageScalarModel S (b r) k).left), ∀ r,
    IsPullback (qK r) (bK r) (stageScalarModel S (b r) k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) ∧
    qK r ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) (b r) = qI r ∧
    GeometricallyConnected (stageScalarModel S (b r) k).hom ∧
    ∀ (L : Type u) [Field L] (ρ : k.val →+* L),
      ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom ρ))
        (stageScalarModel S (b r) k).hom : Scheme.{u})

private theorem common_curve_results
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} [Fintype J] {I IK : J → Scheme.{u}}
    (b : ∀ r, I r ⟶ Spec (.of S)) (bK : ∀ r, IK r ⟶ Spec (.of K))
    (qI : ∀ r, IK r ⟶ I r)
    (hI : ∀ r, IsPullback (qI r) (bK r) (b r)
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hc : ∀ r, curveFibreResult S (b r) (bK r) (qI r))
    (start : CoefficientStage S) : familyCurveResult S b bK qI start := by
  classical
  have hgc : ∀ r, ∃ k, GeometricallyConnected (stageScalarModel S (b r) k).hom := by
    intro r
    obtain ⟨k, _, _, _, hg, _⟩ := hc r
    exact ⟨k, hg⟩
  choose k hk using hgc
  obtain ⟨l, hl, hkl⟩ := curveFamily_upper_stage k start
  have hgl : ∀ r, GeometricallyConnected (stageScalarModel S (b r) l).hom := by
    intro r
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (stageScalarCartesian S (b r) (hkl r)) (hk r)
  let E (r : J) := curveCoefficientIso
    (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (M := Over.mk (b r)) (bK r) (qI r) (hI r)
  let qK (r : J) : IK r ⟶ (stageScalarModel S (b r) l).left :=
    (E r).hom.left ≫ genericLeg S (b r) l
  refine ⟨l, hl, qK, ?_⟩
  intro r
  let : GeometricallyConnected (stageScalarModel S (b r) l).hom := hgl r
  refine ⟨overIso_modelStage_cartesian S (b r) l (Over.mk (bK r)) (E r), ?_,
    hgl r, fun L _ ρ => appendModel_field_connected _ L ρ⟩
  exact curveModel_composite_triangle (E r).hom.left (genericLeg S (b r) l) _ _ (qI r)
    (genericLeg_projection S (b r) l) (hI r).flip.isoPullback_hom_snd

/-- A finite family of simple-curve intersections has connected field fibres
at one coefficient stage above the specified stage, on the same models. -/
theorem exists_simpleCurves_connected
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    {J : Type v} [Fintype J] (w v : J → G.weylGroup) (i : J → G.rootBase.support)
    (hw : ∀ r, G.rootBase.IsPos (G.rootSystem.weylGroupToPerm (w r) (i r).val))
    (hwv : ∀ r, WeylBruhatLE G.rootBase (w r) (v r))
    (C F Y : J → Over (Spec (.of S))) [∀ r, LocallyOfFinitePresentation (F r).hom]
    (E : ∀ r, Over.mk (projectiveToSpec S (ULift.{u} (Fin 2))) ≅ C r)
    (d : ∀ r, C r ⟶ F r) (j : ∀ r, Y r ⟶ F r) [∀ r, IsClosedImmersion (j r).left]
    (qC : ∀ r,
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem (i r).val)).scheme ⟶
        (C r).left)
    (qY : ∀ r, (schubertVariety G (v r)).scheme ⟶ (Y r).left)
    (qF : ∀ r, (flagVariety G).scheme ⟶ (F r).left)
    (hC : ∀ r, IsPullback (qC r)
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem (i r).val)).toSpec
      (C r).hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : ∀ r, IsPullback (qY r) (schubertVariety G (v r)).toSpec (Y r).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : ∀ r, IsPullback (qF r) (flagVariety G).toSpec (F r).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hd : ∀ r, (simpleSchubertCurve G (w r) (i r)).left ≫ qF r = qC r ≫ (d r).left)
    (hj : ∀ r, (schubertInclusion G (v r)).left ≫ qF r = qY r ≫ (j r).left)
    (hcoeff : ∀ r, qC r = simpleCurveCoefficientMap S G (i r) ≫ (E r).hom.left)
    (start : CoefficientStage S) :
    let b := fun r => pullback.fst (d r).left (j r).left ≫ (C r).hom
    let bK := fun r => pullback.fst (simpleSchubertCurve G (w r) (i r)).left
      (schubertInclusion G (v r)).left ≫
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem (i r).val)).toSpec
    let qI := fun r => pullback.map (simpleSchubertCurve G (w r) (i r)).left
      (schubertInclusion G (v r)).left (d r).left (j r).left
        (qC r) (qY r) (qF r) (hd r) (hj r)
    familyCurveResult S b bK qI start := by
  apply common_curve_results S
    (fun r => pullback.fst (d r).left (j r).left ≫ (C r).hom) _ _ _ _ start
  · intro r
    exact (paired_model_scalar_pullback
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem (i r).val)).toSpec
      (schubertVariety G (v r)).toSpec (flagVariety G).toSpec
      (C r).hom (Y r).hom (F r).hom
      (simpleSchubertCurve G (w r) (i r)).left (schubertInclusion G (v r)).left
      (d r).left (j r).left (simpleSchubertCurve G (w r) (i r)).w
      (schubertInclusion G (v r)).w (d r).w (j r).w
      (qC r) (qY r) (qF r) (hC r) (hY r) (hF r) (hd r) (hj r)).1
  · intro r
    exact exists_simpleCurve_intersection_gc S hS G (w r) (v r) (i r)
      (hw r) (hwv r) (E r) (d r) (j r)
      (qC r) (qY r) (qF r) (hC r) (hY r) (hF r) (hd r) (hj r) (hcoeff r)

end SchubertGeometry
