import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendRestriction
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint
/-! # The character degree on a projective append chart -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups GroupActions
open AlgebraicGeometry.Scheme.Modules
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
set_option autoImplicit false
noncomputable section
universe u v w
namespace SchubertGeometry.CharacterLine
open private coefficientBase polynomialBase laurentBase leftParameter rightParameter from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
open private simpleFibre from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendMatching
open private affine overlap line chart leftMap rightMap overlapMap overlapMap_right overlapModule
  chartCounit transitionSection
  from OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition
open private CoframeTransport.evaluation_match CoframeTransport.pullCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport
open private coordinate_raw_match right_scalar map_projection adjunct_frame all_two polynomial_cover
  appendPolynomialBorel appendPolynomialBorel_power appendEndpoint appendPolynomialLift
  appendPolynomialLift_endpoint appendPolynomialLift_transition appendFlagModule appendRawCoframe
  appendCoframe appendCoframe_isIso appendCoordinate from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoframes
open private leftRestrictionValue twistedRestrictionValue storedLeftDefinition
  storedTwistedDefinition from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendRestriction
private abbrev module_comp {X : Scheme.{u}} {M N P : X.Modules}
    (f : Scheme.Modules.Hom M N) (g : Scheme.Modules.Hom N P) : Scheme.Modules.Hom M P :=
  @CategoryStruct.comp X.Modules (inferInstance : CategoryStruct X.Modules) M N P f g
/- A chart frame of a map into the transition module, over arbitrary categories. The transpose
in `hk` keeps its own target object, so at the chart it can be the one in the coordinate's
definition. -/
private theorem frame_of {C D : Type v} [Category.{w} C] [Category.{w} D] {F : C ⥤ D} {H : D ⥤ C}
    (adj : F ⊣ H) {W X : C} {N N' : D} (m : W ⟶ X) (π : X ⟶ H.obj N) (k : W ⟶ H.obj N)
    (e : F.obj W ⟶ N) (t : F.obj X ⟶ N) {e' : F.obj W ⟶ N'}
    (ht : t = F.map π ≫ adj.counit.app N) (hm : m ≫ π = k)
    (hk : HEq k (adj.homEquiv W N' e')) (hN : N' = N) (he : HEq e' e) :
    F.map m ≫ t = e := by
  subst hN
  obtain rfl := eq_of_heq he
  rw [ht, ← Category.assoc, ← F.map_comp, hm, eq_of_heq hk]
  exact adjunct_frame adj W N' e'

/- The chart isomorphisms in counit form. The counit of `restrictAdjunction` agrees with the one in
the chart maps only componentwise, so the comparison is made on sections. -/
private theorem chart_hom_zero (C : Type u) [CommRing C] (d : ℕ) :
    (ProjectiveLine.projectiveTransitionChart C d ⟨0⟩).hom =
      (restrictFunctor (projectiveLinePolynomialChart C ⟨0⟩)).map
          (pullback.fst (ProjectiveLine.leftRestriction C) (ProjectiveLine.twistedRestriction C d))
            ≫
        (restrictAdjunction (projectiveLinePolynomialChart C ⟨0⟩)).counit.app _ := by
  ext U x
  rfl

private theorem chart_hom_one (C : Type u) [CommRing C] (d : ℕ) :
    (ProjectiveLine.projectiveTransitionChart C d ⟨1⟩).hom =
      (restrictFunctor (projectiveLinePolynomialChart C ⟨1⟩)).map
          (pullback.snd (ProjectiveLine.leftRestriction C) (ProjectiveLine.twistedRestriction C d))
            ≫
        (restrictAdjunction (projectiveLinePolynomialChart C ⟨1⟩)).counit.app _ := by
  ext U x
  rfl

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)
private theorem evaluation_scalar_match {L : Scheme.{u}} (chi : G.characters)
    (P Q : Over (Spec (.of K))) (f₀ f₁ : Q ⟶ P) (c₀ c₁ : P.left ⟶ L)
    (r : L ⟶ (flagVariety G).scheme) (h : f₁.left ≫ c₁ = f₀.left ≫ c₀)
    (a₀ a₁ : P ⟶ (reductiveVariety G).toOver)
    (ha₀ : a₀.left ≫ flagQuotient G = c₀ ≫ r)
    (ha₁ : a₁.left ≫ flagQuotient G = c₁ ≫ r)
    (b : Q ⟶ (borelVariety G).toOver)
    (hab : f₀ ≫ a₀ = (f₁ ≫ a₁) * (b ≫ borelInclusion G))
    (e₀ : (Scheme.Modules.pullback c₀).obj
      ((Scheme.Modules.pullback r).obj (flagCharacterModule G chi)) ⟶
        SheafOfModules.unit P.left.ringCatSheaf)
    (e₁ : (Scheme.Modules.pullback c₁).obj
      ((Scheme.Modules.pullback r).obj (flagCharacterModule G chi)) ⟶
        SheafOfModules.unit P.left.ringCatSheaf)
    (he₀ : e₀ = (pullbackComp c₀ r).hom.app (flagCharacterModule G chi) ≫
      characterFrameEvaluation G chi P (c₀ ≫ r) a₀ ha₀)
    (he₁ : e₁ = (pullbackComp c₁ r).hom.app (flagCharacterModule G chi) ≫
      characterFrameEvaluation G chi P (c₁ ≫ r) a₁ ha₁)
    (v : Γ(Q.left, ⊤)) (hv : b.left.appTop (borelCharacterSection G chi) = v) :
    CoframeTransport.pullCoframe f₀.left c₀
        ((Scheme.Modules.pullback r).obj (flagCharacterModule G chi)) e₀ =
      (pullbackCongr h.symm).hom.app ((Scheme.Modules.pullback r).obj
        (flagCharacterModule G chi)) ≫
      CoframeTransport.pullCoframe f₁.left c₁
        ((Scheme.Modules.pullback r).obj (flagCharacterModule G chi)) e₁ ≫
      globalSectionsSmul (SheafOfModules.unit Q.left.ringCatSheaf) v := by
  rw [he₀, he₁]
  have he := CoframeTransport.evaluation_match G chi P Q f₀ f₁ c₀ c₁ r h a₀ a₁ ha₀ ha₁ b hab
  exact right_scalar (C := Q.left.Modules) _ _ _ _ _ he
    (congrArg (globalSectionsSmul (SheafOfModules.unit Q.left.ringCatSheaf)) hv)

private theorem coordinate_wrapped_match {P Q X : Scheme.{u}} (c₀ c₁ : P ⟶ X)
    [IsOpenImmersion c₀] [IsOpenImmersion c₁] (f₀ f₁ : Q ⟶ P)
    (h : f₁ ≫ c₁ = f₀ ≫ c₀) (M : X.Modules)
    (e₀ : (Scheme.Modules.pullback c₀).obj M ⟶ SheafOfModules.unit P.ringCatSheaf)
    (e₁ : (Scheme.Modules.pullback c₁).obj M ⟶ SheafOfModules.unit P.ringCatSheaf)
    (s : SheafOfModules.unit Q.ringCatSheaf ⟶ SheafOfModules.unit Q.ringCatSheaf)
    (hm : CoframeTransport.pullCoframe f₀ c₀ M e₀ = (pullbackCongr h.symm).hom.app M ≫
      CoframeTransport.pullCoframe f₁ c₁ M e₁ ≫ s)
    (k₀ : Scheme.Modules.Hom M ((pushforward c₀).obj (SheafOfModules.unit P.ringCatSheaf)))
    (k₁ : Scheme.Modules.Hom M ((pushforward c₁).obj (SheafOfModules.unit P.ringCatSheaf)))
    (l₀ : Scheme.Modules.Hom ((pushforward c₀).obj (SheafOfModules.unit P.ringCatSheaf))
      ((pushforward (f₀ ≫ c₀)).obj (SheafOfModules.unit Q.ringCatSheaf)))
    (l₁ : Scheme.Modules.Hom ((pushforward c₁).obj (SheafOfModules.unit P.ringCatSheaf))
      ((pushforward (f₀ ≫ c₀)).obj (SheafOfModules.unit Q.ringCatSheaf)))
    (hk₀ : k₀ = (restrictAdjunction c₀).homEquiv M _
      ((restrictFunctorIsoPullback c₀).hom.app M ≫ e₀))
    (hk₁ : k₁ = (restrictAdjunction c₁).homEquiv M _
      ((restrictFunctorIsoPullback c₁).hom.app M ≫ e₁))
    (hl₀ : l₀ = (pushforward c₀).map
      (SheafOfModules.unitToPushforwardObjUnit f₀.toRingCatSheafHom) ≫
        (pushforwardComp f₀ c₀).hom.app _)
    (hl₁ : l₁ = ((pushforward c₁).map
      (SheafOfModules.unitToPushforwardObjUnit f₁.toRingCatSheafHom) ≫
        (pushforwardComp f₁ c₁).hom.app _ ≫ (pushforwardCongr h).hom.app _) ≫
          (pushforward (f₀ ≫ c₀)).map s) :
    @Eq (Scheme.Modules.Hom M ((pushforward (f₀ ≫ c₀)).obj
      (SheafOfModules.unit Q.ringCatSheaf)))
      (module_comp (X := X) k₀ l₀) (module_comp (X := X) k₁ l₁) := by
  rw [hk₀, hk₁, hl₀, hl₁]
  exact coordinate_raw_match c₀ c₁ f₀ f₁ h M e₀ e₁ s hm

private theorem coordinates_from_lifts (chi : G.characters)
    (P Q L : Scheme.{u}) (bp : P ⟶ Spec (.of K)) (bq : Q ⟶ Spec (.of K))
    (f₀ f₁ : Q ⟶ P) (w₀ : f₀ ≫ bp = bq) (w₁ : f₁ ≫ bp = bq)
    (c₀ c₁ : P ⟶ L) [IsOpenImmersion c₀] [IsOpenImmersion c₁]
    (r : L ⟶ (flagVariety G).scheme) (o : Q ⟶ L)
    (h₀ : f₀ ≫ c₀ = o) (h₁ : f₁ ≫ c₁ = o)
    (a₀ a₁ : Over.mk bp ⟶ (reductiveVariety G).toOver)
    (ha₀ : a₀.left ≫ flagQuotient G = c₀ ≫ r)
    (ha₁ : a₁.left ≫ flagQuotient G = c₁ ≫ r)
    (b : Over.mk bq ⟶ (borelVariety G).toOver)
    (hab : (Over.homMk f₀ w₀ : Over.mk bq ⟶ Over.mk bp) ≫ a₀ =
      ((Over.homMk f₁ w₁ : Over.mk bq ⟶ Over.mk bp) ≫ a₁) * (b ≫ borelInclusion G))
    {M T : L.Modules}
    (e₀ : (Scheme.Modules.pullback c₀).obj M ⟶ SheafOfModules.unit P.ringCatSheaf)
    (e₁ : (Scheme.Modules.pullback c₁).obj M ⟶ SheafOfModules.unit P.ringCatSheaf)
    (k₀ : Scheme.Modules.Hom M ((pushforward c₀).obj (SheafOfModules.unit P.ringCatSheaf)))
    (k₁ : Scheme.Modules.Hom M ((pushforward c₁).obj (SheafOfModules.unit P.ringCatSheaf)))
    (l₀ : Scheme.Modules.Hom ((pushforward c₀).obj (SheafOfModules.unit P.ringCatSheaf)) T)
    (l₁ : Scheme.Modules.Hom ((pushforward c₁).obj (SheafOfModules.unit P.ringCatSheaf)) T)
    (hM : M = (Scheme.Modules.pullback r).obj (flagCharacterModule G chi))
    (hT : T = (pushforward o).obj (SheafOfModules.unit Q.ringCatSheaf))
    {Fa₀ Fb₀ Fa₁ Fb₁ : (flagVariety G).scheme.Modules ⥤ P.Modules}
    {π₀ : Fa₀ ≅ Fb₀} {π₁ : Fa₁ ≅ Fb₁}
    {ev₀ : Fb₀.obj (flagCharacterModule G chi) ⟶ SheafOfModules.unit P.ringCatSheaf}
    {ev₁ : Fb₁.obj (flagCharacterModule G chi) ⟶ SheafOfModules.unit P.ringCatSheaf}
    (he₀ : HEq e₀ (π₀.hom.app (flagCharacterModule G chi) ≫ ev₀))
    (he₁ : HEq e₁ (π₁.hom.app (flagCharacterModule G chi) ≫ ev₁))
    (hFa₀ : Fa₀ = Scheme.Modules.pullback r ⋙ Scheme.Modules.pullback c₀)
    (hFa₁ : Fa₁ = Scheme.Modules.pullback r ⋙ Scheme.Modules.pullback c₁)
    (hFb₀ : Fb₀ = Scheme.Modules.pullback (c₀ ≫ r)) (hFb₁ : Fb₁ = Scheme.Modules.pullback (c₁ ≫ r))
    (hπ₀ : HEq π₀ (pullbackComp c₀ r)) (hπ₁ : HEq π₁ (pullbackComp c₁ r))
    (hev₀ : HEq ev₀ (characterFrameEvaluation G chi (Over.mk bp) (c₀ ≫ r) a₀ ha₀))
    (hev₁ : HEq ev₁ (characterFrameEvaluation G chi (Over.mk bp) (c₁ ≫ r) a₁ ha₁))
    {U₀ U₁ : P.Modules}
    {adj₀ : restrictFunctor c₀ ⊣ pushforward c₀} {adj₁ : restrictFunctor c₁ ⊣ pushforward c₁}
    {Ra₀ Rb₀ Ra₁ Rb₁ : L.Modules ⥤ P.Modules} {ρ₀ : Ra₀ ≅ Rb₀} {ρ₁ : Ra₁ ≅ Rb₁}
    {q₀ : Rb₀.obj M ⟶ SheafOfModules.unit P.ringCatSheaf}
    {q₁ : Rb₁.obj M ⟶ SheafOfModules.unit P.ringCatSheaf}
    {u₀ : (restrictFunctor c₀).obj M ⟶ U₀} {u₁ : (restrictFunctor c₁).obj M ⟶ U₁}
    (hk₀ : HEq k₀ (adj₀.homEquiv M U₀ u₀)) (hk₁ : HEq k₁ (adj₁.homEquiv M U₁ u₁))
    (hu₀ : HEq u₀ (ρ₀.hom.app M ≫ q₀)) (hu₁ : HEq u₁ (ρ₁.hom.app M ≫ q₁))
    (hq₀ : HEq q₀ e₀) (hq₁ : HEq q₁ e₁)
    (hU₀ : U₀ = SheafOfModules.unit P.ringCatSheaf) (hU₁ : U₁ = SheafOfModules.unit P.ringCatSheaf)
    (hadj₀ : adj₀ = restrictAdjunction c₀) (hadj₁ : adj₁ = restrictAdjunction c₁)
    (hRa₀ : Ra₀ = restrictFunctor c₀) (hRa₁ : Ra₁ = restrictFunctor c₁)
    (hRb₀ : Rb₀ = Scheme.Modules.pullback c₀) (hRb₁ : Rb₁ = Scheme.Modules.pullback c₁)
    (hρ₀ : HEq ρ₀ (restrictFunctorIsoPullback c₀)) (hρ₁ : HEq ρ₁ (restrictFunctorIsoPullback c₁))
    (v : Γ(Q, ⊤)) (hv : b.left.appTop (borelCharacterSection G chi) = v)
    (hl₀ : HEq l₀ (leftRestrictionValue c₀ f₀))
    (hl₁ : HEq l₁ (twistedRestrictionValue c₁ f₁ o h₁ v)) :
    @Eq (Scheme.Modules.Hom M T)
      (module_comp (X := L) k₀ l₀) (module_comp (X := L) k₁ l₁) := by
  subst M
  subst T
  subst o
  subst hFa₀ hFa₁ hFb₀ hFb₁ hU₀ hU₁ hadj₀ hadj₁ hRa₀ hRa₁ hRb₀ hRb₁
  obtain rfl := eq_of_heq hπ₀
  obtain rfl := eq_of_heq hπ₁
  obtain rfl := eq_of_heq hρ₀
  obtain rfl := eq_of_heq hρ₁
  obtain rfl := eq_of_heq hev₀
  obtain rfl := eq_of_heq hev₁
  have hq₀ := (eq_of_heq hq₀).symm
  have hq₁ := (eq_of_heq hq₁).symm
  subst hq₀ hq₁
  obtain rfl := eq_of_heq hu₀
  obtain rfl := eq_of_heq hu₁
  have hk₀ := eq_of_heq hk₀
  have hk₁ := eq_of_heq hk₁
  have hm := evaluation_scalar_match G chi (Over.mk bp) (Over.mk bq)
    (Over.homMk f₀ w₀) (Over.homMk f₁ w₁) c₀ c₁ r h₁ a₀ a₁ ha₀ ha₁ b hab
    e₀ e₁ (eq_of_heq he₀) (eq_of_heq he₁) v hv
  exact coordinate_wrapped_match c₀ c₁ f₀ f₁ h₁
    ((Scheme.Modules.pullback r).obj (flagCharacterModule G chi)) e₀ e₁
    (globalSectionsSmul (SheafOfModules.unit Q.ringCatSheaf) v) hm
    k₀ k₁ l₀ l₁ hk₀ hk₁ (eq_of_heq hl₀) (eq_of_heq hl₁)

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

private theorem appendCoordinates_match (N : ℕ) :
    @Eq (Scheme.Modules.Hom
      (appendFlagModule G word i U c A p (G.positiveRootCharacter ^ N)) (overlapModule A))
      (module_comp (X := line A)
        (appendCoordinate G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0)
        (ProjectiveLine.leftRestriction A))
      (module_comp (X := line A)
        (appendCoordinate G word i U g a c hend A p (G.positiveRootCharacter ^ N) 1)
        (ProjectiveLine.twistedRestriction A (2 * N))) := by
  exact coordinates_from_lifts G (G.positiveRootCharacter ^ N)
    (affine A) (overlap A) (line A) (polynomialBase A).hom (laurentBase A).hom
    (leftMap A) (rightMap A) (leftParameter A).w (rightParameter A).w
    (chart A ⟨0⟩) (chart A ⟨1⟩) (appendEndpoint G word i U c A p)
    (overlapMap A) rfl (overlapMap_right A)
    (appendPolynomialLift G i U g a A p 0) (appendPolynomialLift G i U g a A p 1)
    (appendPolynomialLift_endpoint G word i U g a c hend A p 0)
    (appendPolynomialLift_endpoint G word i U g a c hend A p 1)
    (appendPolynomialBorel G i A) (appendPolynomialLift_transition G i U g a A p)
    (M := appendFlagModule G word i U c A p (G.positiveRootCharacter ^ N))
    (T := overlapModule A)
    (appendRawCoframe G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0)
    (appendRawCoframe G word i U g a c hend A p (G.positiveRootCharacter ^ N) 1)
    (appendCoordinate G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0)
    (appendCoordinate G word i U g a c hend A p (G.positiveRootCharacter ^ N) 1)
    (ProjectiveLine.leftRestriction A) (ProjectiveLine.twistedRestriction A (2 * N))
    rfl rfl HEq.rfl HEq.rfl rfl rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    (U₀ := SheafOfModules.unit (polynomialBase A).left.ringCatSheaf)
    (U₁ := SheafOfModules.unit (polynomialBase A).left.ringCatSheaf)
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl rfl rfl rfl rfl rfl rfl rfl rfl HEq.rfl HEq.rfl
    (transitionSection A (2 * N)) (appendPolynomialBorel_power G N i A)
    (storedLeftDefinition A) (storedTwistedDefinition A (2 * N))

/- The degree map is chosen from this existence statement rather than written as `pullback.lift`:
a definition abstracts the proofs nested in its value, including the `NeZero` proofs of the chart
indices, and the kernel then compares the abstracted coordinates with the stated ones inside `≫`,
where it evaluates them at the projective line. -/
private theorem appendDegreeMap_exists (N : ℕ) :
    ∃ m : appendFlagModule G word i U c A p (G.positiveRootCharacter ^ N) ⟶
        ProjectiveLine.projectiveTransitionModule A (2 * N),
      m ≫ pullback.fst _ _ = appendCoordinate G word i U g a c hend A p _ 0 ∧
        m ≫ pullback.snd _ _ = appendCoordinate G word i U g a c hend A p _ 1 :=
  ⟨pullback.lift _ _ (appendCoordinates_match G word i U g a c hend A p N),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

private def appendDegreeMap (N : ℕ) :
    appendFlagModule G word i U c A p (G.positiveRootCharacter ^ N) ⟶
      ProjectiveLine.projectiveTransitionModule A (2 * N) :=
  Classical.choose (appendDegreeMap_exists G word i U g a c hend A p N)

private theorem frame_zero (N : ℕ) :
    (restrictFunctor (projectiveLinePolynomialChart A ⟨0⟩)).map
        (appendDegreeMap G word i U g a c hend A p N) ≫
        (ProjectiveLine.projectiveTransitionChart A (2 * N) ⟨0⟩).hom =
      appendCoframe G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0 := by
  exact frame_of (restrictAdjunction (projectiveLinePolynomialChart A ⟨0⟩))
    (appendDegreeMap G word i U g a c hend A p N)
    (pullback.fst (ProjectiveLine.leftRestriction A) (ProjectiveLine.twistedRestriction A (2 * N)))
    (appendCoordinate G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0) (appendCoframe G
      word i U g a c hend A p (G.positiveRootCharacter ^ N) 0)
    (ProjectiveLine.projectiveTransitionChart A (2 * N) ⟨0⟩).hom (chart_hom_zero A (2 * N))
    (Classical.choose_spec (appendDegreeMap_exists G word i U g a c hend A p N)).1 HEq.rfl rfl
      HEq.rfl

private theorem frame_one (N : ℕ) :
    (restrictFunctor (projectiveLinePolynomialChart A ⟨1⟩)).map
        (appendDegreeMap G word i U g a c hend A p N) ≫
        (ProjectiveLine.projectiveTransitionChart A (2 * N) ⟨1⟩).hom =
      appendCoframe G word i U g a c hend A p (G.positiveRootCharacter ^ N) 1 := by
  exact frame_of (restrictAdjunction (projectiveLinePolynomialChart A ⟨1⟩))
    (appendDegreeMap G word i U g a c hend A p N)
    (pullback.snd (ProjectiveLine.leftRestriction A) (ProjectiveLine.twistedRestriction A (2 * N)))
    (appendCoordinate G word i U g a c hend A p (G.positiveRootCharacter ^ N) 1) (appendCoframe G
      word i U g a c hend A p (G.positiveRootCharacter ^ N) 1)
    (ProjectiveLine.projectiveTransitionChart A (2 * N) ⟨1⟩).hom (chart_hom_one A (2 * N))
    (Classical.choose_spec (appendDegreeMap_exists G word i U g a c hend A p N)).2 HEq.rfl rfl
      HEq.rfl

private theorem appendDegreeMap_frame (N : ℕ) (j : Fin 2) :
    (restrictFunctor (projectiveLinePolynomialChart A ⟨j⟩)).map
        (appendDegreeMap G word i U g a c hend A p N) ≫
        (ProjectiveLine.projectiveTransitionChart A (2 * N) ⟨j⟩).hom =
      appendCoframe G word i U g a c hend A p (G.positiveRootCharacter ^ N) j :=
  all_two (fun j => (restrictFunctor (projectiveLinePolynomialChart A ⟨j⟩)).map
        (appendDegreeMap G word i U g a c hend A p N) ≫
        (ProjectiveLine.projectiveTransitionChart A (2 * N) ⟨j⟩).hom =
      appendCoframe G word i U g a c hend A p (G.positiveRootCharacter ^ N) j)
    (frame_zero G word i U g a c hend A p N) (frame_one G word i U g a c hend A p N) j

private theorem appendDegreeMap_isIso (N : ℕ) :
    IsIso (appendDegreeMap G word i U g a c hend A p N) := by
  apply FrobeniusSplitting.isIso_on_open_family
    (fun _ : ULift.{u} (Fin 2) => Spec (.of (Polynomial A)))
    (projectiveLinePolynomialChart A) (polynomial_cover A) _
  rintro ⟨j⟩
  have he := appendDegreeMap_frame G word i U g a c hend A p N j
  let _ := appendCoframe_isIso G word i U g a c hend A p (G.positiveRootCharacter ^ N) j
  let _ := ((ProjectiveLine.projectiveTransitionChart A (2 * N) ⟨j⟩).isIso_hom)
  exact IsIso.of_isIso_fac_right he

/-- The original character line has degree twice its exponent on the specified append chart. -/
def appendCharacterDegreeIso (N : ℕ) :
    (Scheme.Modules.pullback (projectiveAppendChart G i A p c)).obj
        (wordCharacterModule G (G.positiveRootCharacter ^ N) (word ++ [i])) ≅
      ProjectiveLine.projectiveTransitionModule A (2 * N) := by
  let he : IsIso (appendDegreeMap G word i U g a c hend A p N) :=
    appendDegreeMap_isIso G word i U g a c hend A p N
  exact (pullbackComp (projectiveAppendChart G i A p c)
    (bsdhMap G (word ++ [i]))).app (flagCharacterModule G (G.positiveRootCharacter ^ N)) ≪≫
      @asIso _ _ _ _ (appendDegreeMap G word i U g a c hend A p N) he

end Append


end SchubertGeometry.CharacterLine
