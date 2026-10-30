import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendDegree
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.PolynomialSections
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalDetection
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.DeterminantSection
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.RightmostCoefficient
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport
import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
/-! # The original determinant section in append polynomial coordinates -/

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.CharacterLine
open TauCeti
set_option autoImplicit false
noncomputable section
universe u v w
namespace SchubertGeometry.CharacterLine

open private coefficientBase polynomialBase baseParameter polynomialParameter
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
open private coefficientPair appendEndpoint appendPolynomialLift appendEvaluation appendRawCoframe
  appendCoframe appendCoordinate appendPolynomialLift_endpoint appendFlagModule spec_scalar
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoframes
open private appendDegreeMap appendDegreeMap_frame appendDegreeMap_exists appendDegreeMap_isIso
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendDegree
open private appendLift fibreSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendMatching
open private universalPoint constantPoint from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.RightmostCoefficient
open private CoframeTransport.algebraMapOver from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport
open private polynomialGa from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
open private chart_adjunction_unit chart_adjunction_projection from
  OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalCoordinates
open private cancel_iso_frame pullSection pullSection_comp from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private evaluationAdjunct from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.FrameRule

private theorem spectrum_value {R H A B : Type u} [CommRing R] [CommRing H]
    [CommRing A] [CommRing B] [Bialgebra R H] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A)) :
    Spec.mapMulEquiv (AlgHom.mapValue f g) = CoframeTransport.algebraMapOver f ≫ Spec.mapMulEquiv g := by
  apply CategoryTheory.Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (f.comp g.ofConv).toRingHom) =
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom g.ofConv.toRingHom)
  exact Spec.map_comp (CommRingCat.ofHom g.ofConv.toRingHom) (CommRingCat.ofHom f.toRingHom)

private theorem triple_map {H J : Type v} [Monoid H] [Monoid J]
    (f : H →* J) (x y z : H) : f x * (f y * f z) = f ((x * y) * z) := by
  rw [map_mul, map_mul, mul_assoc]

private theorem translate_right {C : Type v} [Category.{w} C] [CartesianMonoidalCategory C]
    {X H : C} [GrpObj H] (f : X ⟶ H) (g : 𝟙_ C ⟶ H) :
    f ≫ (GrpObj.mulRight g).hom = f * (toUnit X ≫ g) := by
  simp only [GrpObj.mulRight, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc,
    Hom.mul_def]

private theorem lift_multiply {C : Type v} [Category.{w} C] [CartesianMonoidalCategory C]
    {X A B H : C} [MonObj H] (a : X ⟶ A) (b : X ⟶ B) (r : A ⟶ H) (t : B ⟶ H) :
    lift a b ≫ ((fst A B ≫ r) * (snd A B ≫ t)) = (a ≫ r) * (b ≫ t) := by
  simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]

private theorem adjoint_compare {C D : Type v} [Category.{w} C] [Category.{w} D]
    {F P : C ⥤ D} {H : D ⥤ C} (a : F ⊣ H) (b : P ⊣ H)
    (M : C) (N : D) (e : P.obj M ⟶ N) :
    a.homEquiv M N ((a.leftAdjointUniq b).hom.app M ≫ e) = b.homEquiv M N e :=
  (a.homEquiv_naturality_right _ e).trans
    ((congrArg (fun t => t ≫ H.map e) (a.homEquiv_leftAdjointUniq_hom_app b M)).trans
      (b.homEquiv_unit M N e).symm)

/- `adjoint_compare` with the transpose and the restriction comparison taken as they occur in a
coordinate's definition; the equations `hF`, `ha`, `hρ` then compare whole terms. -/
private theorem transpose_section {C D : Type v} [Category.{w} C] [Category.{w} D]
    {F F₁ F₂ P : C ⥤ D} {H : D ⥤ C} (a : F ⊣ H) (b : P ⊣ H)
    {U M : C} {N : D} (t : U ⟶ M) (e : P.obj M ⟶ N)
    {a₁ : F₁ ⊣ H} {ρ : F₂ ≅ P} {u : F₁.obj M ⟶ N} (k : M ⟶ H.obj N)
    (hk : k = a₁.homEquiv M N u) (hu : HEq u (ρ.hom.app M ≫ e))
    (hF₁ : F₁ = F) (hF₂ : F₂ = F) (ha : HEq a₁ a) (hρ : HEq ρ (a.leftAdjointUniq b)) :
    t ≫ k = t ≫ b.homEquiv M N e := by
  subst hF₁ hF₂
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hρ
  obtain rfl := eq_of_heq hu
  subst hk
  rw [adjoint_compare]

private theorem section_projection {C D : Type v} [Category.{w} C] [Category.{w} D]
    {F : C ⥤ D} {H : D ⥤ C} (a : F ⊣ H) {U M : C} {N : D}
    (s : U ⟶ M) (e : F.obj M ⟶ N) (eta : F.obj U ⟶ N)
    (k : M ⟶ H.obj N) (u : U ⟶ H.obj N) (v : N ⟶ N)
    (he : a.homEquiv M N e = k) (hu : a.homEquiv U N eta = u)
    (hs : F.map s ≫ e = eta ≫ v) : s ≫ k = u ≫ H.map v :=
  (congrArg (fun t => s ≫ t) he.symm).trans
    ((a.homEquiv_naturality_left s e).symm.trans
      ((congrArg (a.homEquiv U N) hs).trans
        ((a.homEquiv_naturality_right eta v).trans (congrArg (fun t => t ≫ H.map v) hu))))

private theorem section_adjunct {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf) (r : Γ(X, ⊤))
    (h : pullSection f M s ≫ e = globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r) :
    s ≫ (pullbackPushforwardAdjunction f).homEquiv M _ e =
      relativeCoefficient Y (Over.mk f) r := by
  have he : (Scheme.Modules.pullback f).map s ≫ e =
      (pullbackObjUnitIso f).hom ≫ globalSectionsSmul _ r := by
    have hh := congrArg (fun t => (pullbackObjUnitIso f).hom ≫ t) h
    exact (Iso.hom_inv_id_assoc (pullbackObjUnitIso f) _).symm.trans
      ((congrArg (fun t => (pullbackObjUnitIso f).hom ≫ t) (Category.assoc _ _ _).symm).trans hh)
  exact ((pullbackPushforwardAdjunction f).homEquiv_naturality_left s e).symm.trans
    ((congrArg ((pullbackPushforwardAdjunction f).homEquiv _ _) he).trans
      (((pullbackPushforwardAdjunction f).homEquiv_naturality_right (pullbackObjUnitIso f).hom _).trans
        (congrArg (fun t => t ≫ (pushforward f).map (globalSectionsSmul _ r))
          (pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom f))))

private theorem matched_section {C : Type v} [Category.{w} C] {U A B M T : C}
    (s : U ⟶ A) (e : A ⟶ B) (k : B ⟶ T) (t : U ⟶ M)
    (f : M ⟶ B) (c : M ⟶ T) (r : U ⟶ T)
    (he : s ≫ e = t ≫ f) (hf : f ≫ k = c) (hc : t ≫ c = r) : (s ≫ e) ≫ k = r :=
  (congrArg (fun z => z ≫ k) he).trans
    ((Category.assoc t f k).trans ((congrArg (fun z => t ≫ z) hf).trans hc))

private theorem section_evaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (r : Γ(X, ⊤))
    (h : s ≫ (pullbackPushforwardAdjunction f).homEquiv M _ e =
      relativeCoefficient Y (Over.mk f) r) :
    pullSection f M s ≫ e = globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r := by
  let U := pullbackObjUnitIso f
  let adj := pullbackPushforwardAdjunction f
  let t := globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r
  have hr : adj.homEquiv (SheafOfModules.unit Y.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) (U.hom ≫ t) =
        relativeCoefficient Y (Over.mk f) r :=
    (adj.homEquiv_naturality_right U.hom t).trans
      (congrArg (fun z => z ≫ (pushforward f).map t)
        (pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom f))
  have he : (Scheme.Modules.pullback f).map s ≫ e = U.hom ≫ t :=
    (adj.homEquiv _ _).injective
      ((adj.homEquiv_naturality_left s e).trans (h.trans hr.symm))
  exact ((Category.assoc U.inv ((Scheme.Modules.pullback f).map s) e).trans
    (congrArg (fun z => U.inv ≫ z) he)).trans
      ((Category.assoc U.inv U.hom t).symm.trans
        ((congrArg (fun z => z ≫ t) U.inv_hom_id).trans (Category.id_comp t)))

private theorem compose_section {C : Type v} [Category.{w} C] {A B D E : C}
    (s : A ⟶ B) (e : B ⟶ D) (i : B ⟶ E) (f : E ⟶ D)
    (t : A ⟶ E) (r : A ⟶ D) (he : e = i ≫ f)
    (hs : s ≫ i = t) (hr : t ≫ f = r) : s ≫ e = r :=
  (congrArg (fun z => s ≫ z) he).trans
    ((Category.assoc s i f).symm.trans
      ((congrArg (fun z => z ≫ f) hs).trans hr))

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def framePullback (A : CommAlgCat.{u} K)
    (a : coefficientBase A ⟶ (oppositeUnipotentVariety G).toOver)
    (g : G.points) : G.coordinateAlgebra →+* A :=
  (Spec.preimage (show Spec (.of A) ⟶ Spec (.of G.coordinateAlgebra) from
    (a ≫ flagChartMap G g).left)).hom
private def framePolynomial (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (a : coefficientBase A ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) : Polynomial A :=
  Polynomial.map (framePullback G A a g)
    (DeterminantSection.simpleFramePolynomial G i (DeterminantSection.positiveDetCoefficient G))
private theorem frame_degree (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (a : coefficientBase A ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) :
    (framePolynomial G i A a g).natDegree ≤ 2 :=
  Polynomial.natDegree_map_le.trans (DeterminantSection.simpleFrame_degree G i)

private theorem frame_adjunct (chi : G.characters)
    (X : Over (Spec (.of K))) (m : X.left ⟶ (flagVariety G).scheme)
    (k : X ⟶ (reductiveVariety G).toOver) (hk : k.left ≫ flagQuotient G = m) :
    (pullbackPushforwardAdjunction m).homEquiv (flagCharacterModule G chi)
        (SheafOfModules.unit X.left.ringCatSheaf)
        (characterFrameEvaluation G chi X m k hk) =
      flagCharacterInclusion G chi ≫
        relativeFunctionsMap (flagVariety G).scheme (X := Over.mk m)
          (Y := Over.mk (flagQuotient G)) (Over.homMk k.left hk) :=
  Equiv.apply_symm_apply ((pullbackPushforwardAdjunction m).homEquiv _ _) _

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendDegree: determinantEvaluation"

private theorem determinantEvaluation (N : ℕ)
    (X : Over (Spec (.of K))) (m : X.left ⟶ (flagVariety G).scheme)
    (k : X ⟶ (reductiveVariety G).toOver) (hk : k.left ≫ flagQuotient G = m) :
    pullSection m (flagCharacterModule G (G.positiveRootCharacter ^ N))
        (flagDeterminantModuleSection G N) ≫
        characterFrameEvaluation G (G.positiveRootCharacter ^ N) X m k hk =
      globalSectionsSmul (SheafOfModules.unit X.left.ringCatSheaf)
        (k.left.appTop (DeterminantSection.positiveDetPowerFunction G N)) := by
  apply section_evaluation m (flagCharacterModule G (G.positiveRootCharacter ^ N))
    (flagDeterminantModuleSection G N) _ _
  exact compose_section (C := (flagVariety G).scheme.Modules) _ _ _ _ _ _
    (frame_adjunct G _ X m k hk)
    (flagDeterminantModuleSection_inclusion G N)
    (relativeCoefficient_pullback (flagVariety G).scheme
      (Over.homMk (U := Over.mk m) (V := Over.mk (flagQuotient G)) k.left hk)
      (DeterminantSection.positiveDetPowerFunction G N))

private theorem spectrum_ga (i : G.rootBase.support) (A : CommAlgCat.{u} K) :
    polynomialParameter A ≫ gaMorphism G (G.simpleRootMap i) =
      Spec.mapMulEquiv (gaParameterPoint (G.simpleRootMap i) (Polynomial.X : Polynomial A)) := by
  have h : (Polynomial.mapAlgHom (Algebra.ofId K A)).comp (gaPolynomialEquiv K).toAlgHom =
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := Polynomial A)).symm
        (Multiplicative.ofAdd Polynomial.X)).ofConv := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext_ring
    simp [gaPolynomialEquiv_generator]
  have he := congrArg (fun f : SymmetricAlgebra K K →ₐ[K] Polynomial A =>
    f.comp (G.simpleRootMap i).toAlgHom) h
  apply CategoryTheory.Over.OverMorphism.ext
  rw [CommHopfAlgCat.mapMulEquiv_left]
  change (Spec.map (CommRingCat.ofHom (Polynomial.mapAlgHom (Algebra.ofId K A)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (gaPolynomialEquiv K).toAlgHom.toRingHom)) ≫
        ((algSpec (CommRingCat.of K)).map
          (CommAlgCat.ofHom (G.simpleRootMap i).toAlgHom).op).left = _
  rw [algSpec_map_left_ofAlgHom, ← Spec.map_comp]
  exact (Spec.map_comp _ _).symm.trans (congrArg (fun f : G.coordinateAlgebra →ₐ[K] Polynomial A =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) he)

omit [IsAlgClosed K] [CharZero K] in
private theorem spectrum_constant (A : CommAlgCat.{u} K) (n : G.points) :
    toUnit (polynomialBase A) ≫
      (reductiveVariety G).pointsEquivOverHom (reductivePointsMulEquiv G n) =
        Spec.mapMulEquiv (AlgHom.mapValue (Algebra.ofId K (Polynomial A)) n) := by
  apply CategoryTheory.Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial A))) ≫
      Spec.map (CommRingCat.ofHom n.ofConv.toRingHom) =
    Spec.map (CommRingCat.ofHom ((Algebra.ofId K (Polynomial A)).comp n.ofConv).toRingHom)
  exact (Spec.map_comp _ _).symm

private def prefixPoint (A : CommAlgCat.{u} K)
    (b : coefficientBase A ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) :
    WithConv (G.coordinateAlgebra →ₐ[K] A) :=
  Spec.mapMulEquiv.symm (b ≫ flagChartMap G g)

private def polynomialFamily (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (b : coefficientBase A ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) :
    WithConv (G.coordinateAlgebra →ₐ[K] Polynomial A) :=
  AlgHom.mapValue (Polynomial.CAlgHom (R := K) (A := A)) (prefixPoint G A b g) *
    gaParameterPoint (G.simpleRootMap i) Polynomial.X *
      AlgHom.mapValue (Algebra.ofId K (Polynomial A)) (G.reflectionPoint i.val)⁻¹

private theorem polynomialFamily_map (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (b : coefficientBase A ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) :
    (polynomialFamily G i A b g).ofConv =
      (Polynomial.mapAlgHom (prefixPoint G A b g).ofConv).comp
        (DeterminantSection.simpleFramePolynomial G i) := by
  let f := Polynomial.mapAlgHom (prefixPoint G A b g).ofConv
  have hu : AlgHom.mapValue f (universalPoint G) =
      AlgHom.mapValue (Polynomial.CAlgHom (R := K) (A := A)) (prefixPoint G A b g) := by
    apply WithConv.ofConv_injective
    ext x
    simp [f, universalPoint, AlgHom.mapValue_apply]
  have hn : AlgHom.mapValue f (constantPoint G (G.reflectionPoint i.val)⁻¹) =
      AlgHom.mapValue (Algebra.ofId K (Polynomial A)) (G.reflectionPoint i.val)⁻¹ := by
    rw [constantPoint, ← MonoidHom.comp_apply, ← AlgHom.mapValue_comp, Algebra.comp_ofId]
  change _ = (AlgHom.mapValue f (universalPoint G *
    gaParameterPoint (G.simpleRootMap i) Polynomial.X *
      constantPoint G (G.reflectionPoint i.val)⁻¹)).ofConv
  rw [map_mul, map_mul, gaParameterPoint_mapValue, hu, hn]
  simp only [f, Polynomial.coe_mapAlgHom, Polynomial.map_X]
  rfl

private theorem polynomialLift_family (i : G.rootBase.support) (U : Over (Spec (.of K)))
    (g : G.points) (a : U ⟶ (oppositeUnipotentVariety G).toOver)
    (A : CommAlgCat.{u} K) (p : coefficientBase A ⟶ U) :
    appendPolynomialLift G i U g a A p 0 =
      Spec.mapMulEquiv (polynomialFamily G i A (p ≫ a) g) := by
  have hp : baseParameter A ≫ ((p ≫ a) ≫ flagChartMap G g) =
      Spec.mapMulEquiv (AlgHom.mapValue (Polynomial.CAlgHom (R := K) (A := A))
        (prefixPoint G A (p ≫ a) g)) :=
    (congrArg (fun f => baseParameter A ≫ f)
      (Spec.mapMulEquiv.apply_symm_apply ((p ≫ a) ≫ flagChartMap G g)).symm).trans
        (spectrum_value (Polynomial.CAlgHom (R := K) (A := A))
          (prefixPoint G A (p ≫ a) g)).symm
  have ht := translate_right (polynomialParameter A ≫ gaMorphism G (G.simpleRootMap i))
    ((reductiveVariety G).pointsEquivOverHom
      (reductivePointsMulEquiv G ((G.reflectionPoint i.val)⁻¹)))
  have hx := congrArg₂ (fun f h => f * h) (spectrum_ga G i A)
    (spectrum_constant G A ((G.reflectionPoint i.val)⁻¹))
  have hb := lift_multiply (baseParameter A ≫ p) (polynomialParameter A)
    (a ≫ flagChartMap G g) (simplePositiveSection G i)
  have hp' := (Category.assoc (baseParameter A) p (a ≫ flagChartMap G g)).trans
    ((congrArg (fun t => baseParameter A ≫ t) (Category.assoc p a (flagChartMap G g)).symm).trans hp)
  exact hb.trans ((congrArg₂ (fun f h => f * h) hp'
    ((Category.assoc (polynomialParameter A) (gaMorphism G (G.simpleRootMap i))
      (rightTranslation (reductiveVariety G)
        (reductivePointsMulEquiv G ((G.reflectionPoint i.val)⁻¹))).hom).symm.trans
          (ht.trans hx))).trans
            (triple_map Spec.mapMulEquiv.toMonoidHom _ _ _))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendSections: polynomialLift_value"

private theorem polynomialLift_value (N : ℕ) (i : G.rootBase.support)
    (U : Over (Spec (.of K))) (g : G.points)
    (a : U ⟶ (oppositeUnipotentVariety G).toOver)
    (A : CommAlgCat.{u} K) (p : coefficientBase A ⟶ U) :
    (appendPolynomialLift G i U g a A p 0).left.appTop
        (DeterminantSection.positiveDetPowerFunction G N) =
      (Scheme.ΓSpecIso (.of (Polynomial A))).inv (framePolynomial G i A (p ≫ a) g ^ N) := by
  have hfamily := polynomialLift_family G i U g a A p
  have hvalue : (polynomialFamily G i A (p ≫ a) g).ofConv
      (DeterminantSection.positiveDetPower G N) = framePolynomial G i A (p ≫ a) g ^ N := by
    rw [polynomialFamily_map]
    change Polynomial.map (prefixPoint G A (p ≫ a) g).ofConv.toRingHom
        (DeterminantSection.simpleFramePolynomial G i
          (DeterminantSection.positiveDetCoefficient G ^ N)) =
      (Polynomial.map (framePullback G A (p ≫ a) g)
        (DeterminantSection.simpleFramePolynomial G i (DeterminantSection.positiveDetCoefficient G))) ^ N
    rw [map_pow, Polynomial.map_pow]
    rfl
  exact (congrArg (fun k : polynomialBase A ⟶ (reductiveVariety G).toOver =>
      k.left.appTop (DeterminantSection.positiveDetPowerFunction G N)) hfamily).trans
    ((spec_scalar (polynomialFamily G i A (p ≫ a) g).ofConv.toRingHom
      (DeterminantSection.positiveDetPower G N)).trans
        (congrArg (fun t : Polynomial A => (Scheme.ΓSpecIso (.of (Polynomial A))).inv t) hvalue))

private theorem framePower_degree (N : ℕ) (i : G.rootBase.support)
    (A : CommAlgCat.{u} K)
    (b : coefficientBase A ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) :
    (framePolynomial G i A b g ^ N).natDegree ≤ 2 * N :=
  (Polynomial.natDegree_pow_le_of_le N (frame_degree G i A b g)).trans
    (le_of_eq (Nat.mul_comm N 2))

/-- The translated quadratic power gives its global section of degree twice the exponent. -/
def appendPolynomialSection (N : ℕ) (i : G.rootBase.support) (A : CommAlgCat.{u} K)
    (b : coefficientBase A ⟶ (oppositeUnipotentVariety G).toOver) (g : G.points) :
    SheafOfModules.unit (projectiveScheme A (ULift.{u} (Fin 2))).ringCatSheaf ⟶
      ProjectiveLine.projectiveTransitionModule A (2 * N) :=
  ProjectiveLine.projectivePolynomialSection A (2 * N) (framePolynomial G i A b g ^ N)
    (framePower_degree G N i A b g)

section Append
variable (word : List G.rootBase.support) (i : G.rootBase.support)
  (U : Over (Spec (.of K))) (g : G.points)
  (a : U ⟶ (oppositeUnipotentVariety G).toOver)
  (c : U ⊗ (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
    Over.mk (bsdhToSpec G (word ++ [i])))
  (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
    CategoryTheory.Limits.pullback.snd (bsdhMap G word)
      (flagBundleProjection G (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a ⊗ₘ 𝟙 (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
        flagBundleChart G (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)) g)
  (A : CommAlgCat.{u} K) (p : coefficientBase A ⟶ U)

/- The original section against the raw coframe on the first polynomial chart. -/
private theorem appendRaw_section (N : ℕ) :
    pullSection (projectiveLinePolynomialChart A ⟨0⟩) ((Scheme.Modules.pullback (appendEndpoint G word i U c A p)).obj (flagCharacterModule G (G.positiveRootCharacter ^ N))) (pullSection (appendEndpoint G word i U c A p) (flagCharacterModule G (G.positiveRootCharacter ^ N)) (flagDeterminantModuleSection G N)) ≫
        appendRawCoframe G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0 =
      globalSectionsSmul (SheafOfModules.unit (polynomialBase A).left.ringCatSheaf)
        ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (framePolynomial G i A (p ≫ a) g ^ N)) := by
  have hv := (cancel_iso_frame (D := (polynomialBase A).left.Modules)
    ((pullbackComp (projectiveLinePolynomialChart A ⟨0⟩) (appendEndpoint G word i U c A p)).app (flagCharacterModule G (G.positiveRootCharacter ^ N)))
    (pullSection_comp (projectiveLinePolynomialChart A ⟨0⟩) (appendEndpoint G word i U c A p) (flagCharacterModule G (G.positiveRootCharacter ^ N)) (flagDeterminantModuleSection G N))
    (appendEvaluation G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0)).trans
      ((determinantEvaluation G N (polynomialBase A) ((projectiveLinePolynomialChart A ⟨0⟩) ≫ (appendEndpoint G word i U c A p))
        (appendPolynomialLift G i U g a A p 0)
        (appendPolynomialLift_endpoint G word i U g a c hend A p 0)).trans
          (congrArg (globalSectionsSmul (SheafOfModules.unit (polynomialBase A).left.ringCatSheaf))
            (polynomialLift_value G N i U g a A p)))
  have hraw : appendRawCoframe G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0 =
      ((pullbackComp (projectiveLinePolynomialChart A ⟨0⟩) (appendEndpoint G word i U c A p)).app (flagCharacterModule G (G.positiveRootCharacter ^ N))).hom ≫ appendEvaluation G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0 := rfl
  exact (congrArg (fun e => pullSection (projectiveLinePolynomialChart A ⟨0⟩) ((Scheme.Modules.pullback (appendEndpoint G word i U c A p)).obj (flagCharacterModule G (G.positiveRootCharacter ^ N))) (pullSection (appendEndpoint G word i U c A p) (flagCharacterModule G (G.positiveRootCharacter ^ N)) (flagDeterminantModuleSection G N)) ≫ e) hraw).trans hv

/- The coordinate is the pullback transpose of the raw coframe. Kept apart from the section
computation: as one proof with the chart data bound by `let`, the kernel check exceeds its
budget. -/
private theorem appendCoordinate_transpose (N : ℕ) :
    (pullSection (appendEndpoint G word i U c A p) (flagCharacterModule G (G.positiveRootCharacter ^ N)) (flagDeterminantModuleSection G N)) ≫ appendCoordinate G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0 =
      (pullSection (appendEndpoint G word i U c A p) (flagCharacterModule G (G.positiveRootCharacter ^ N)) (flagDeterminantModuleSection G N)) ≫ (pullbackPushforwardAdjunction (X := (polynomialBase A).left) (projectiveLinePolynomialChart A ⟨0⟩)).homEquiv
        (appendFlagModule G word i U c A p (G.positiveRootCharacter ^ N)) (SheafOfModules.unit (polynomialBase A).left.ringCatSheaf)
        (appendRawCoframe G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0) :=
  transpose_section (restrictAdjunction (X := (polynomialBase A).left) (projectiveLinePolynomialChart A ⟨0⟩))
      (pullbackPushforwardAdjunction (X := (polynomialBase A).left) (projectiveLinePolynomialChart A ⟨0⟩))
      (M := appendFlagModule G word i U c A p (G.positiveRootCharacter ^ N))
      (N := SheafOfModules.unit (polynomialBase A).left.ringCatSheaf) _
      (appendRawCoframe G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0) (appendCoordinate G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0)
      rfl HEq.rfl rfl rfl HEq.rfl HEq.rfl

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendSections: appendOriginal_coordinate"

private theorem appendOriginal_coordinate (N : ℕ) :
    pullSection (appendEndpoint G word i U c A p)
        (flagCharacterModule G (G.positiveRootCharacter ^ N)) (flagDeterminantModuleSection G N) ≫
      appendCoordinate G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0 =
    relativeCoefficient (projectiveScheme A (ULift.{u} (Fin 2)))
      (Over.mk (projectiveLinePolynomialChart A ⟨0⟩))
      ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (framePolynomial G i A (p ≫ a) g ^ N)) :=
  (appendCoordinate_transpose G word i U g a c hend A p N).trans
    (section_adjunct (X := (polynomialBase A).left) (projectiveLinePolynomialChart A ⟨0⟩)
      (appendFlagModule G word i U c A p (G.positiveRootCharacter ^ N)) _
      (appendRawCoframe G word i U g a c hend A p (G.positiveRootCharacter ^ N) 0) _ (appendRaw_section G word i U g a c hend A p N))

/- The determinant section is assembled from separately checked pieces, each comparing the
definitions as whole terms; checked together inside one proof, the comparisons exceed the
kernel's budget. -/
private theorem appendDeterminant_left (N : ℕ) :
    (pullSection (projectiveAppendChart G i A p c) ((Scheme.Modules.pullback (bsdhMap G (word ++ [i]))).obj (flagCharacterModule G (G.positiveRootCharacter ^ N)))
        (pullSection (bsdhMap G (word ++ [i])) (flagCharacterModule G (G.positiveRootCharacter ^ N)) (flagDeterminantModuleSection G N)) ≫
      ((pullbackComp (projectiveAppendChart G i A p c) (bsdhMap G (word ++ [i]))).app (flagCharacterModule G (G.positiveRootCharacter ^ N))).hom ≫ appendDegreeMap G word i U g a c hend A p N) ≫ (ProjectiveLine.projectiveTransitionEmbed A (2 * N)) =
    relativeCoefficient (projectiveScheme A (ULift.{u} (Fin 2)))
      (Over.mk (projectiveLinePolynomialChart A ⟨0⟩))
      ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (framePolynomial G i A (p ≫ a) g ^ N)) :=
  matched_section (C := (projectiveScheme A (ULift.{u} (Fin 2))).Modules) _ _ (ProjectiveLine.projectiveTransitionEmbed A (2 * N)) _ _ _ _
    (cancel_iso_frame (D := (projectiveScheme A (ULift.{u} (Fin 2))).Modules)
      ((pullbackComp (projectiveAppendChart G i A p c) (bsdhMap G (word ++ [i]))).app (flagCharacterModule G (G.positiveRootCharacter ^ N)))
      (pullSection_comp (projectiveAppendChart G i A p c) (bsdhMap G (word ++ [i])) (flagCharacterModule G (G.positiveRootCharacter ^ N)) (flagDeterminantModuleSection G N))
      (appendDegreeMap G word i U g a c hend A p N))
    (Classical.choose_spec (appendDegreeMap_exists G word i U g a c hend A p N)).1
    (appendOriginal_coordinate G word i U g a c hend A p N)

private theorem appendPolynomial_right (N : ℕ) : type_of% (section_projection
    (C := (projectiveScheme A (ULift.{u} (Fin 2))).Modules)
    (D := (polynomialBase A).left.Modules)
    (restrictAdjunction (projectiveLinePolynomialChart A ⟨0⟩))
    (appendPolynomialSection G N i A (p ≫ a) g)
    (ProjectiveLine.projectiveTransitionChart A (2 * N) ⟨0⟩).hom
    (restrictUnitIso (projectiveLinePolynomialChart A ⟨0⟩)).hom (ProjectiveLine.projectiveTransitionEmbed A (2 * N)) _ _
    (chart_adjunction_projection A (2 * N)) (chart_adjunction_unit (projectiveLinePolynomialChart A ⟨0⟩))
    (ProjectiveLine.projectivePolynomialSection_left A (2 * N)
      (framePolynomial G i A (p ≫ a) g ^ N) (framePower_degree G N i A (p ≫ a) g))) :=
  section_projection
    (C := (projectiveScheme A (ULift.{u} (Fin 2))).Modules)
    (D := (polynomialBase A).left.Modules)
    (restrictAdjunction (projectiveLinePolynomialChart A ⟨0⟩))
    (appendPolynomialSection G N i A (p ≫ a) g)
    (ProjectiveLine.projectiveTransitionChart A (2 * N) ⟨0⟩).hom
    (restrictUnitIso (projectiveLinePolynomialChart A ⟨0⟩)).hom (ProjectiveLine.projectiveTransitionEmbed A (2 * N)) _ _
    (chart_adjunction_projection A (2 * N)) (chart_adjunction_unit (projectiveLinePolynomialChart A ⟨0⟩))
    (ProjectiveLine.projectivePolynomialSection_left A (2 * N)
      (framePolynomial G i A (p ≫ a) g ^ N) (framePower_degree G N i A (p ≫ a) g))

private theorem appendCoefficient_unfold (N : ℕ) :
    relativeCoefficient (projectiveScheme A (ULift.{u} (Fin 2)))
      (Over.mk (projectiveLinePolynomialChart A ⟨0⟩))
      ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (framePolynomial G i A (p ≫ a) g ^ N)) =
    SheafOfModules.unitToPushforwardObjUnit (projectiveLinePolynomialChart A ⟨0⟩).toRingCatSheafHom ≫
      FrobeniusSplitting.CharacterLine.relativeFunctionsSmul (projectiveScheme A (ULift.{u} (Fin 2)))
        (Over.mk (projectiveLinePolynomialChart A ⟨0⟩))
        ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (framePolynomial G i A (p ≫ a) g ^ N)) := rfl

private theorem appendWord_section (N : ℕ) :
    pullSection (projectiveAppendChart G i A p c) (wordCharacterModule G (G.positiveRootCharacter ^ N) (word ++ [i]))
        (wordDeterminantModuleSection G N (word ++ [i])) =
      pullSection (projectiveAppendChart G i A p c) ((Scheme.Modules.pullback (bsdhMap G (word ++ [i]))).obj (flagCharacterModule G (G.positiveRootCharacter ^ N)))
        (pullSection (bsdhMap G (word ++ [i])) (flagCharacterModule G (G.positiveRootCharacter ^ N)) (flagDeterminantModuleSection G N)) := rfl

private theorem appendDegreeIso_hom (N : ℕ) :
    (appendCharacterDegreeIso G word i U g a c hend A p N).hom =
      ((pullbackComp (projectiveAppendChart G i A p c) (bsdhMap G (word ++ [i]))).app (flagCharacterModule G (G.positiveRootCharacter ^ N))).hom ≫ appendDegreeMap G word i U g a c hend A p N :=
  (Iso.trans_hom _ _).trans (congrArg (fun z => ((pullbackComp (projectiveAppendChart G i A p c)
    (bsdhMap G (word ++ [i]))).app (flagCharacterModule G (G.positiveRootCharacter ^ N))).hom ≫ z)
      (@asIso_hom _ _ _ _ (appendDegreeMap G word i U g a c hend A p N) (appendDegreeMap_isIso G word i U g a c hend A p N)))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "AppendSections: appendDeterminant_section"

/-- The original determinant section becomes the full translated quadratic power on the append chart. -/
theorem appendDeterminant_section (N : ℕ) :
    pullSection (projectiveAppendChart G i A p c)
        (wordCharacterModule G (G.positiveRootCharacter ^ N) (word ++ [i]))
        (wordDeterminantModuleSection G N (word ++ [i])) ≫
      (appendCharacterDegreeIso G word i U g a c hend A p N).hom =
        appendPolynomialSection G N i A (p ≫ a) g := by
  have := ProjectiveLine.projectiveTransitionEmbed_mono A (2 * N)
  apply (cancel_mono (ProjectiveLine.projectiveTransitionEmbed A (2 * N))).mp
  exact (congrArg₂ (fun x y => (x ≫ y) ≫ (ProjectiveLine.projectiveTransitionEmbed A (2 * N))) (appendWord_section G word i U c A p N) (appendDegreeIso_hom G word i U g a c hend A p N)).trans
    ((appendDeterminant_left G word i U g a c hend A p N).trans ((appendCoefficient_unfold G i U g a A p N).trans (rfl.trans (appendPolynomial_right G i U g a A p N).symm)))

end Append
end SchubertGeometry.CharacterLine
