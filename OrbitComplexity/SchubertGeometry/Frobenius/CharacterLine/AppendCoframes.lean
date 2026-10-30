import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsScheme
import OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterPowers
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport
/-! # Character coframes on a projective append chart -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open AlgebraicGeometry.Scheme.Modules
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
set_option autoImplicit false
noncomputable section
universe u v w
namespace SchubertGeometry.CharacterLine
open private coefficientBase polynomialBase baseParameter polynomialParameter polynomialPair
  polynomialPair_chart laurentCoefficient laurentBase leftParameter rightParameter laurentTorus
    laurentToBase
  leftParameter_polynomial rightParameter_polynomial leftParameter_base rightParameter_base from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
open private simpleFibre fibreChart appendChart appendLift appendLift_endpoint
  appendLift_transition
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendMatching
open private leftMap rightMap overlapMap overlapMap_right chartModule overlapModule chartCounit
  transitionSection
  leftChartMap_isIso rightChartMap_isIso from
  OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition
open private power_transition from
  OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterPowers
open private CoframeTransport.coordinate_match CoframeTransport.evaluation_match
  CoframeTransport.pullCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport
open private compIsIso from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.LiftEvaluation
private theorem prefix_cancel {C : Type v} [Category.{w} C] {A B D : C}
    (e : A ≅ B) (f : B ⟶ D) : e.inv ≫ (e.hom ≫ f) = f :=
  (Category.assoc e.inv e.hom f).symm.trans
    ((congrArg (fun t => t ≫ f) e.inv_hom_id).trans (Category.id_comp f))
private theorem group_right {C : Type v} [Category.{w} C] {A B D E F H : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (e : F ⟶ H) :
    a ≫ b ≫ c ≫ d ≫ e = a ≫ ((b ≫ c ≫ d) ≫ e) := by simp only [Category.assoc]
private theorem coordinate_raw_match {P Q X : Scheme.{u}} (c₀ c₁ : P ⟶ X)
    [IsOpenImmersion c₀] [IsOpenImmersion c₁] (f₀ f₁ : Q ⟶ P)
    (h : f₁ ≫ c₁ = f₀ ≫ c₀) (M : X.Modules)
    (e₀ : (Scheme.Modules.pullback c₀).obj M ⟶ SheafOfModules.unit P.ringCatSheaf)
    (e₁ : (Scheme.Modules.pullback c₁).obj M ⟶ SheafOfModules.unit P.ringCatSheaf)
    (s : SheafOfModules.unit Q.ringCatSheaf ⟶ SheafOfModules.unit Q.ringCatSheaf)
    (hm : CoframeTransport.pullCoframe f₀ c₀ M e₀ = (pullbackCongr h.symm).hom.app M ≫
      CoframeTransport.pullCoframe f₁ c₁ M e₁ ≫ s) :
    (restrictAdjunction c₀).homEquiv M _
        ((restrictFunctorIsoPullback c₀).hom.app M ≫ e₀) ≫
        (pushforward c₀).map (SheafOfModules.unitToPushforwardObjUnit f₀.toRingCatSheafHom) ≫
        (pushforwardComp f₀ c₀).hom.app _ =
      (restrictAdjunction c₁).homEquiv M _
        ((restrictFunctorIsoPullback c₁).hom.app M ≫ e₁) ≫
        (((pushforward c₁).map (SheafOfModules.unitToPushforwardObjUnit f₁.toRingCatSheafHom) ≫
          (pushforwardComp f₁ c₁).hom.app _ ≫ (pushforwardCongr h).hom.app _) ≫
          (pushforward (f₀ ≫ c₀)).map s) := by
  have hm' := (congrArg (CoframeTransport.pullCoframe f₀ c₀ M)
    (prefix_cancel ((restrictFunctorIsoPullback c₀).app M) e₀)).trans
      (hm.trans (congrArg (fun e => (pullbackCongr h.symm).hom.app M ≫
        CoframeTransport.pullCoframe f₁ c₁ M e ≫ s)
          (prefix_cancel ((restrictFunctorIsoPullback c₁).app M) e₁).symm))
  have hc := CoframeTransport.coordinate_match c₀ c₁ f₀ f₁ h M
    ((restrictFunctorIsoPullback c₀).hom.app M ≫ e₀)
    ((restrictFunctorIsoPullback c₁).hom.app M ≫ e₁) s hm'
  exact hc.trans (group_right _ _ _ _ _)
private theorem map_projection {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F : C ⥤ D) {W X Y : C} {T : D}
    (l : W ⟶ X) (p : X ⟶ Y) (c : W ⟶ Y) (e : F.obj Y ⟶ T)
    (h : l ≫ p = c) : F.map l ≫ F.map p ≫ e = F.map c ≫ e :=
  ((Category.assoc (F.map l) (F.map p) e).symm.trans
    (congrArg (fun t => t ≫ e) (F.map_comp l p).symm)).trans
      (congrArg (fun t => F.map t ≫ e) h)
private theorem adjunct_frame {C D : Type v} [Category.{w} C] [Category.{w} D]
    {F : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (M : C) (N : D)
    (e : F.obj M ⟶ N) : F.map (adj.homEquiv M N e) ≫ adj.counit.app N = e :=
  (adj.homEquiv M N).symm_apply_apply e
private theorem all_two (P : Fin 2 → Prop) (h₀ : P 0) (h₁ : P 1) : ∀ j, P j := by
  intro j
  fin_cases j
  · exact h₀
  · exact h₁
private theorem right_scalar {C : Type v} [Category.{w} C] {A B D : C}
    (u : A ⟶ D) (v : A ⟶ B) (w : B ⟶ D) (s t : D ⟶ D)
    (h : u = v ≫ w ≫ s) (hs : s = t) : u = v ≫ w ≫ t :=
  h.trans (congrArg (fun a => v ≫ w ≫ a) hs)
private theorem spec_scalar {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) :
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) =
      (Scheme.ΓSpecIso (.of S)).inv (f r) :=
  (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) r).symm
open private chart_covers from OrbitComplexity.GroupActions.Varieties.ProjectiveChartsScheme
private theorem polynomial_cover (R : Type u) [CommRing R]
    (x : projectiveScheme R (ULift.{u} (Fin 2))) :
    ∃ (j : ULift.{u} (Fin 2)) (y : Spec (.of (Polynomial R))),
      projectiveLinePolynomialChart R j y = x := by
  obtain ⟨j, y, hy⟩ := chart_covers R (ULift.{u} (Fin 2)) x
  have hx : x ∈ (projectiveChartMap R (ULift.{u} (Fin 2)) j).opensRange := ⟨y, hy⟩
  have hx' : x ∈ (projectiveLinePolynomialChart R j).opensRange := by
    rw [projectiveLinePolynomialChart_range, ← projectiveChartMap_range]
    exact hx
  exact ⟨j, hx'⟩
private theorem pair_square {C : Type v} [Category.{w} C] [CartesianMonoidalCategory C]
    {A B D E X : C} (a : X ⟶ A) (b : X ⟶ B) (p : A ⟶ D) (q : B ⟶ E) :
    lift a (b ≫ q) ≫ (p ⊗ₘ 𝟙 E) = lift (a ≫ p) b ≫ (𝟙 D ⊗ₘ q) := by
  simp only [lift_map, Category.comp_id]
private theorem mapped_pair {C : Type v} [Category.{w} C] [CartesianMonoidalCategory C]
    {W X A B D : C} (f : W ⟶ X) (a : X ⟶ A) (b : X ⟶ B)
    (c : W ⟶ A) (d : W ⟶ D) (t : D ⟶ B)
    (ha : f ≫ a = c) (hb : f ≫ b = d ≫ t) :
    f ≫ lift a b = lift c d ≫ (𝟙 A ⊗ₘ t) := by
  simp only [comp_lift, ha, hb, lift_map, Category.comp_id]
private theorem chart_pair_comp {C : Type v} [Category.{w} C] {A B D E T : C}
    (x : A ⟶ B) (e : B ⟶ D) (z : A ⟶ D) (f : D ⟶ E) (g : E ⟶ T)
    (h : x ≫ e = z) : x ≫ (e ≫ (f ≫ g)) = (z ≫ f) ≫ g :=
  ((Category.assoc x e (f ≫ g)).symm.trans
    (congrArg (fun a => a ≫ (f ≫ g)) h)).trans (Category.assoc z f g).symm
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)
omit [IsAlgClosed K] [CharZero K] in
private def coefficientPair (A : CommAlgCat.{u} K) (U : Over (Spec (.of K)))
    (p : coefficientBase A ⟶ U) :
    polynomialBase A ⟶ U ⊗ (additiveVariety K).toOver :=
  lift (baseParameter A ≫ p) (polynomialParameter A)
omit [IsAlgClosed K] [CharZero K] in
private def laurentPair (A : CommAlgCat.{u} K) (U : Over (Spec (.of K)))
    (p : coefficientBase A ⟶ U) :
    laurentBase A ⟶ U ⊗
      (affineVariety K (MonoidAlgebra K (Multiplicative ℤ))).toOver :=
  lift (laurentToBase A ≫ p) (laurentTorus A)
omit [IsAlgClosed K] [CharZero K] in
private theorem coefficientPair_left (A : CommAlgCat.{u} K) (U : Over (Spec (.of K)))
    (p : coefficientBase A ⟶ U) :
    leftParameter A ≫ coefficientPair A U p =
      laurentPair A U p ≫ (𝟙 U ⊗ₘ ProjectiveLine.multiplicativeParameter (K := K) 1) :=
  mapped_pair (leftParameter A) (baseParameter A ≫ p) (polynomialParameter A)
    (laurentToBase A ≫ p) (laurentTorus A)
    (ProjectiveLine.multiplicativeParameter (K := K) 1)
    ((Category.assoc (leftParameter A) (baseParameter A) p).symm.trans
      (congrArg (fun e => e ≫ p) (leftParameter_base A)))
    (leftParameter_polynomial A)
omit [IsAlgClosed K] [CharZero K] in
private theorem coefficientPair_right (A : CommAlgCat.{u} K) (U : Over (Spec (.of K)))
    (p : coefficientBase A ⟶ U) :
    rightParameter A ≫ coefficientPair A U p =
      laurentPair A U p ≫ (𝟙 U ⊗ₘ ProjectiveLine.multiplicativeParameter (K := K) (-1)) :=
  mapped_pair (rightParameter A) (baseParameter A ≫ p) (polynomialParameter A)
    (laurentToBase A ≫ p) (laurentTorus A)
    (ProjectiveLine.multiplicativeParameter (K := K) (-1))
    ((Category.assoc (rightParameter A) (baseParameter A) p).symm.trans
      (congrArg (fun e => e ≫ p) (rightParameter_base A)))
    (rightParameter_polynomial A)
private def appendPolynomialBorel (i : G.rootBase.support) (A : CommAlgCat.{u} K) :
    laurentBase A ⟶ (borelVariety G).toOver :=
  laurentTorus A ≫ ProjectiveLine.simpleOverlapMorphism G i
private theorem appendPolynomialBorel_power (N : ℕ) (i : G.rootBase.support)
    (A : CommAlgCat.{u} K) :
    (appendPolynomialBorel G i A).left.appTop
        (borelCharacterSection G (G.positiveRootCharacter ^ N)) =
      (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).inv
        (LaurentPolynomial.T ((2 * N : ℕ) : ℤ)) := by
  have h : (appendPolynomialBorel G i A).left.appTop
      (borelCharacterSection G (G.positiveRootCharacter ^ N)) =
      (laurentCoefficient A).left.appTop
        (ProjectiveLine.characterModuleSection G i (G.positiveRootCharacter ^ N)) := rfl
  exact h.trans ((congrArg (fun t => (laurentCoefficient A).left.appTop t)
    (power_transition G N i)).trans
      ((spec_scalar (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId K A)).toRingHom
        (LaurentPolynomial.T ((2 * N : ℕ) : ℤ))).trans
          (congrArg (fun t : LaurentPolynomial A =>
            (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).inv t)
              ((AddMonoidAlgebra.mapAlgHom_single (Algebra.ofId K A)
                ((2 * N : ℕ) : ℤ) (1 : K)).trans
                  (congrArg (fun a : A => AddMonoidAlgebra.single ((2 * N : ℕ) : ℤ) a)
                    (map_one (Algebra.ofId K A)))))))
section Append
variable (word : List G.rootBase.support) (i : G.rootBase.support)
  (U : Over (Spec (.of K))) (g : G.points)
  (a : U ⟶ (oppositeUnipotentVariety G).toOver)
  (c : U ⊗ (simpleFibre G i).toOver ⟶ Over.mk (bsdhToSpec G (word ++ [i])))
  (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
    pullback.snd (bsdhMap G word) (flagBundleProjection G (simpleFibre G i)) =
      (a ⊗ₘ 𝟙 (simpleFibre G i).toOver).left ≫
        flagBundleChart G (simpleFibre G i) g)
  (A : CommAlgCat.{u} K) (p : coefficientBase A ⟶ U)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoframes: appendPolynomialChart"

private theorem appendPolynomialChart (j : Fin 2) :
    projectiveLinePolynomialChart A ⟨j⟩ ≫ projectiveAppendChart G i A p c =
      (coefficientPair A U p ≫ appendChart G word i U c j).left := by
  have hs := congrArg
    (fun f : polynomialBase A ⟶ U ⊗ (simpleFibre G i).toOver => f.left ≫ c.left)
    (pair_square (baseParameter A) (polynomialParameter A) p (fibreChart G i j))
  exact (chart_pair_comp (projectiveLinePolynomialChart A ⟨j⟩)
    (simpleBorelLineIso G i A).inv (polynomialPair G i A j).left
    (p ⊗ₘ 𝟙 (simpleFibre G i).toOver).left c.left
    (polynomialPair_chart G i A j)).trans hs

private abbrev appendEndpoint : projectiveScheme A (ULift.{u} (Fin 2)) ⟶
    (flagVariety G).scheme :=
  projectiveAppendChart G i A p c ≫ bsdhMap G (word ++ [i])

private def appendPolynomialLift (j : Fin 2) :
    polynomialBase A ⟶ (reductiveVariety G).toOver :=
  coefficientPair A U p ≫ appendLift G U g a i j

include hend in
private theorem appendPolynomialLift_endpoint (j : Fin 2) :
    (appendPolynomialLift G i U g a A p j).left ≫ flagQuotient G =
      projectiveLinePolynomialChart A ⟨j⟩ ≫ appendEndpoint G word i U c A p := by
  have he := appendLift_endpoint G word i U g a c hend j
  have hfirst := (Category.assoc (coefficientPair A U p).left
    (appendLift G U g a i j).left (flagQuotient G)).trans
      (congrArg (fun f => (coefficientPair A U p).left ≫ f) he)
  have hlast := congrArg (fun f => f ≫ bsdhMap G (word ++ [i]))
    (appendPolynomialChart G word i U c A p j)
  exact hfirst.trans ((Category.assoc (coefficientPair A U p).left
    (appendChart G word i U c j).left (bsdhMap G (word ++ [i]))).symm.trans
      (hlast.symm.trans (Category.assoc (projectiveLinePolynomialChart A ⟨j⟩)
        (projectiveAppendChart G i A p c) (bsdhMap G (word ++ [i])))))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoframes: appendPolynomialLift_transition"

private theorem appendPolynomialLift_transition :
    leftParameter A ≫ appendPolynomialLift G i U g a A p 0 =
      (rightParameter A ≫ appendPolynomialLift G i U g a A p 1) *
        (appendPolynomialBorel G i A ≫ borelInclusion G) := by
  let q := laurentPair A U p
  let t₀ := 𝟙 U ⊗ₘ ProjectiveLine.multiplicativeParameter (K := K) 1
  let t₁ := 𝟙 U ⊗ₘ ProjectiveLine.multiplicativeParameter (K := K) (-1)
  let beta := snd U
    (affineVariety K (MonoidAlgebra K (Multiplicative ℤ))).toOver ≫
      ProjectiveLine.simpleOverlapMorphism G i
  have h₀ := (Category.assoc (leftParameter A) (coefficientPair A U p)
      (appendLift G U g a i 0)).symm.trans
    ((congrArg (fun e => e ≫ appendLift G U g a i 0)
      (coefficientPair_left A U p)).trans (Category.assoc q t₀ (appendLift G U g a i 0)))
  have h₁ := (Category.assoc (rightParameter A) (coefficientPair A U p)
      (appendLift G U g a i 1)).symm.trans
    ((congrArg (fun e => e ≫ appendLift G U g a i 1)
      (coefficientPair_right A U p)).trans (Category.assoc q t₁ (appendLift G U g a i 1)))
  have hb : q ≫ beta = appendPolynomialBorel G i A :=
    (Category.assoc q _ (ProjectiveLine.simpleOverlapMorphism G i)).symm.trans
      (congrArg (fun e => e ≫ ProjectiveLine.simpleOverlapMorphism G i)
        (lift_snd (laurentToBase A ≫ p) (laurentTorus A)))
  have ht := congrArg (fun f => q ≫ f) (appendLift_transition G U g a i)
  have hm := MonObj.comp_mul q (t₁ ≫ appendLift G U g a i 1) (beta ≫ borelInclusion G)
  have hbeta := (Category.assoc q beta (borelInclusion G)).symm.trans
    (congrArg (fun e => e ≫ borelInclusion G) hb)
  exact h₀.trans (ht.trans (hm.trans (congrArg₂ (fun x y => x * y) h₁.symm hbeta)))

private abbrev appendFlagModule (chi : G.characters) :
    (projectiveScheme A (ULift.{u} (Fin 2))).Modules :=
  (Scheme.Modules.pullback (appendEndpoint G word i U c A p)).obj
    (flagCharacterModule G chi)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoframes: appendPolynomialFrame"

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoframes: appendEvaluation"
private def appendEvaluation (chi : G.characters) (j : Fin 2) :
    (Scheme.Modules.pullback (projectiveLinePolynomialChart A ⟨j⟩ ≫
      appendEndpoint G word i U c A p)).obj (flagCharacterModule G chi) ⟶
        SheafOfModules.unit (polynomialBase A).left.ringCatSheaf :=
  characterFrameEvaluation G chi (polynomialBase A)
    (projectiveLinePolynomialChart A ⟨j⟩ ≫ appendEndpoint G word i U c A p)
    (appendPolynomialLift G i U g a A p j)
    (appendPolynomialLift_endpoint G word i U g a c hend A p j)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoframes: appendRawCoframe"
private def appendRawCoframe (chi : G.characters) (j : Fin 2) :
    (Scheme.Modules.pullback (projectiveLinePolynomialChart A ⟨j⟩)).obj
        (appendFlagModule G word i U c A p chi) ⟶
      SheafOfModules.unit (polynomialBase A).left.ringCatSheaf :=
  (pullbackComp (projectiveLinePolynomialChart A ⟨j⟩)
      (appendEndpoint G word i U c A p)).hom.app (flagCharacterModule G chi) ≫
    appendEvaluation G word i U g a c hend A p chi j

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoframes: appendCoframe"
private def appendCoframe (chi : G.characters) (j : Fin 2) :
    (appendFlagModule G word i U c A p chi).restrict (projectiveLinePolynomialChart A ⟨j⟩) ⟶
      SheafOfModules.unit (polynomialBase A).left.ringCatSheaf :=
  (restrictFunctorIsoPullback (projectiveLinePolynomialChart A ⟨j⟩)).hom.app
      (appendFlagModule G word i U c A p chi) ≫
    appendRawCoframe G word i U g a c hend A p chi j

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendCoframes: appendCoframe_isIso"
private theorem appendCoframe_isIso (chi : G.characters) (j : Fin 2) :
    IsIso (appendCoframe G word i U g a c hend A p chi j) :=
  compIsIso _ _
    (((restrictFunctorIsoPullback (projectiveLinePolynomialChart A ⟨j⟩)).app
      (appendFlagModule G word i U c A p chi)).isIso_hom)
    (compIsIso _ _
      (((pullbackComp (projectiveLinePolynomialChart A ⟨j⟩)
        (appendEndpoint G word i U c A p)).app (flagCharacterModule G chi)).isIso_hom)
      (characterFrameEvaluation_isIso G chi (polynomialBase A)
        (projectiveLinePolynomialChart A ⟨j⟩ ≫ appendEndpoint G word i U c A p)
        (appendPolynomialLift G i U g a A p j)
        (appendPolynomialLift_endpoint G word i U g a c hend A p j)))

private def appendCoordinate (chi : G.characters) (j : Fin 2) :
    appendFlagModule G word i U c A p chi ⟶ chartModule A ⟨j⟩ :=
  (restrictAdjunction (projectiveLinePolynomialChart A ⟨j⟩)).homEquiv _ _
    (appendCoframe G word i U g a c hend A p chi j)

end Append
end SchubertGeometry.CharacterLine
