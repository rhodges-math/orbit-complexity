import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordInductionState
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordPreimageSections
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPreimageGluing
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionCoefficientStage
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.FlatSectionReflection
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.PreimageSectionValues
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Determinant sections on opposite-chart preimages -/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting ReductiveGroups GroupActions
open FrobeniusSplitting.RetainedCharacter FrobeniusSplitting.CharacterLine
open scoped TensorProduct CategoryTheory.MonObj

noncomputable section

namespace SchubertGeometry.RetainedCharacter

open private FrobeniusSplitting.RetainedCharacter.singletonIndex
  FrobeniusSplitting.RetainedCharacter.singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private SchubertGeometry.RetainedCharacter.preimageSnd
  SchubertGeometry.RetainedCharacter.preimageFst
  SchubertGeometry.RetainedCharacter.polynomialSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private scalarMap from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private SchubertGeometry.DeterminantSection.chartAlgebra from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomial
open private wholeComparison from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes
open private SchubertGeometry.CharacterLine.pullSection
  SchubertGeometry.CharacterLine.pullSection_comp SchubertGeometry.CharacterLine.pullSection_congr
    from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames

private theorem section_map {K : Type u} [Field K] {A B : CommRingCat.{u}}
    (f : A ⟶ B) [Algebra K B] [IsReduced B] [Algebra.FiniteType K B]
    (p : A) (q : B) (h : f.hom p = q) (t : Γ(Spec B, ⊤))
    (ht : SchubertGeometry.DeterminantSection.affineSection (K := K) B q = t) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso A).inv.hom p) = t := by
  calc
    _ = (Scheme.ΓSpecIso B).inv.hom (f.hom p) :=
      (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality f) p).symm
    _ = (Scheme.ΓSpecIso B).inv.hom q :=
      congrArg (Scheme.ΓSpecIso B).inv.hom h
    _ = t := ht

private theorem polynomial_section_value {K : Type u}
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support) (n : ℕ) :
    SchubertGeometry.DeterminantSection.affineSection (K := K)
      (Polynomial (SchubertGeometry.DeterminantSection.chartAlgebra G i))
      (SchubertGeometry.DeterminantSection.oppositionChartPolynomial G i n) =
        SchubertGeometry.RetainedCharacter.polynomialSection G i n := by
  unfold SchubertGeometry.RetainedCharacter.polynomialSection
  rfl

open private section_character_laws from
  OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ChosenBorelCharacter

private theorem prefix_coordinate_square
    {K : Type u} [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (M : PrefixModel G word) (s : {s : Finset M.J // s.Nonempty}) :
    Spec.map (M.v.app s) ≫ (M.cG.ι.app (op s)).left =
      (M.fieldCocone.ι.app (op s)).left ≫ M.m₀ := by
  have he : (M.e s).toRingHom.comp
      (Algebra.TensorProduct.includeRight : M.N.obj s →ₐ[M.S] K ⊗[M.S] M.N.obj s).toRingHom =
        (M.v.app s).hom := RingHom.ext (M.eValue s)
  have h := congrArg (fun f : M.N.obj s →+* M.F.obj s =>
    Spec.map (CommRingCat.ofHom f) ≫ (M.cG.ι.app (op s)).left) he
  exact h.symm.trans (M.hbmodel s).symm

set_option maxHeartbeats 400000 in
/-- One retained unit and one coframe stage express every original word section
on the whole opposite-chart preimage as its determinant power. -/
theorem exists_preimage_section_stage
    {K : Type u}
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (M : PrefixModel G word)
    (i : G.rootBase.support) (S0 : Subalgebra ℤ K) (hS0 : S0.FG)
    {M0 : Type u} [hM0 : CommRing M0] [hS0M0 : Algebra S0 M0]
    [hFlatM0 : Module.Flat S0 M0]
    (coefficientIso : K ⊗[S0] M0 ≃ₐ[K] (SchubertGeometry.DeterminantSection.chartAlgebra G i))
    (vars rels : Type u) [hvars : Finite vars] [hrels : Finite rels]
    (presentation : Algebra.Presentation S0 M0 vars rels)
    (start0 : Subalgebra ℤ K) (hstart0 : start0.FG) :
    ∃ (B : Subalgebra ℤ K) (hS0B : S0 ≤ B), start0 ≤ B ∧ B.FG ∧
      let hS0BAlg : Algebra S0 B := (Subalgebra.inclusion hS0B).toAlgebra
      let hS0BTower : IsScalarTower S0 B K := Subalgebra.inclusion.isScalarTower_right hS0B K
      let coefficientMap : B ⊗[S0] M0 →+* (SchubertGeometry.DeterminantSection.chartAlgebra G i) :=
        (@scalarMap S0 B K M0 (SchubertGeometry.DeterminantSection.chartAlgebra G i)
          (inferInstanceAs (CommRing S0)) (inferInstanceAs (CommRing B))
          hK.toCommRing hM0 (inferInstanceAs (CommRing
            (SchubertGeometry.DeterminantSection.chartAlgebra G i)))
          hS0BAlg (inferInstanceAs (Algebra S0 K)) (inferInstanceAs (Algebra B K))
          hS0M0 (inferInstanceAs (Algebra K (SchubertGeometry.DeterminantSection.chartAlgebra G i)))
            hS0BTower coefficientIso)
      let polynomialSource : CommRingCat.{u} := CommRingCat.of (Polynomial (B ⊗[S0] M0))
      let polynomialTarget : CommRingCat.{u} := CommRingCat.of (Polynomial
        (SchubertGeometry.DeterminantSection.chartAlgebra G i))
      let polynomialMap : polynomialSource ⟶
        polynomialTarget :=
        CommRingCat.ofHom (@Polynomial.mapRingHom (B ⊗[S0] M0)
          (SchubertGeometry.DeterminantSection.chartAlgebra G i)
          (inferInstanceAs (Semiring (B ⊗[S0] M0)))
          (inferInstanceAs (Semiring (SchubertGeometry.DeterminantSection.chartAlgebra G i)))
            coefficientMap)
      ∃ w : (B ⊗[S0] M0)ˣ,
      ∀ (Y0 : Scheme.{u}) [CompactSpace Y0]
        (base0 : Y0 ⟶ Spec (.of B)) [Smooth base0]
        (z : wordChartPreimage G word (𝟙 (bsdhScheme G word)) i ⟶ Y0)
        (_hz : IsPullback z
          (SchubertGeometry.RetainedCharacter.preimageSnd G word (𝟙 (bsdhScheme G word)) i ≫
            M.fieldCocone.pt.hom)
          base0 (Spec.map (CommRingCat.ofHom (algebraMap B K))))
        (j0 : Y0 ⟶ M.cG.pt.left)
        (_hwhole : z ≫ j0 = SchubertGeometry.RetainedCharacter.preimageSnd G word (𝟙 (bsdhScheme G
          word)) i ≫ M.m₀)
        (b0 : Y0 ⟶ Spec polynomialSource)
        (_hb0 : z ≫ b0 = SchubertGeometry.RetainedCharacter.preimageFst G word (𝟙 (bsdhScheme G
          word)) i ≫
          Spec.map polynomialMap)
        (start : Subalgebra ℤ K) (_hstart : start.FG),
      ∃ (Tstage : Subalgebra ℤ K) (hBT : B ≤ Tstage),
        start ≤ Tstage ∧ Tstage.FG ∧
        letI : Algebra B Tstage := (Subalgebra.inclusion hBT).toAlgebra
        letI : IsScalarTower B Tstage K := Subalgebra.inclusion.isScalarTower_right hBT K
        ∀ (YT : Scheme.{u}) [YT.IsSeparated]
          (baseT : YT ⟶ Spec (.of Tstage)) [Smooth baseT]
          (qT : YT ⟶ Y0) (nT : wordChartPreimage G word (𝟙 (bsdhScheme G word)) i ⟶ YT)
          (_hbase : nT ≫ qT = z)
          (_hqT : IsPullback qT baseT base0
            (Spec.map (CommRingCat.ofHom (algebraMap B Tstage))))
          (_hnT : IsPullback nT
            (SchubertGeometry.RetainedCharacter.preimageSnd G word (𝟙 (bsdhScheme G word)) i ≫
              M.fieldCocone.pt.hom)
            baseT (Spec.map (CommRingCat.ofHom (algebraMap Tstage K))))
          (n : ℕ),
        ∃ E : ((Scheme.Modules.pullback qT).obj ((Scheme.Modules.pullback j0).obj (matchingModule
          M.N M.cG M.delta n))) ≅ SheafOfModules.unit YT.ringCatSheaf,
          (SchubertGeometry.CharacterLine.pullSection qT ((Scheme.Modules.pullback j0).obj
            (matchingModule M.N M.cG M.delta n)) (SchubertGeometry.CharacterLine.pullSection j0
            (matchingModule M.N M.cG M.delta n) (@coefficientMatchingSection.{u} M.S M.J
            (inferInstanceAs (CommRing M.S)) M.N M.cG M.delta (fun j => (M.P
            (FrobeniusSplitting.RetainedCharacter.singletonIndex j)).coeff 2) M.hr n))) ≫ E.hom =
          globalSectionsSmul (SheafOfModules.unit YT.ringCatSheaf) ((qT ≫ b0).appTop.hom
            ((Scheme.ΓSpecIso polynomialSource).inv.hom ((Polynomial.C (w : B ⊗[S0] M0) *
            (Polynomial.X : Polynomial (B ⊗[S0] M0)) ^ 2) ^ n))) := by
  classical
  have hunit :=
    @SchubertGeometry.DeterminantSection.exists_opposition_coefficient_stage.{u,u}
      K hK hAlg hChar G i S0 hS0 M0 hM0 hS0M0 hFlatM0 coefficientIso
      vars rels hvars hrels presentation start0 hstart0
  obtain ⟨B, hS0B, hstartB, hB, aB, w, _, _, _, hpoly⟩ := hunit
  refine ⟨B, hS0B, hstartB, hB, ?_⟩
  intro hS0BAlg hS0BTower coefficientMap polynomialSource polynomialTarget polynomialMap
  refine ⟨w, ?_⟩
  intro Y0 hcompact base0 hsmooth z hz j0 hwhole b0 hb0 start hstart
  have hcoframes :=
    @exists_preimage_coframes.{u} K hK hAlg hChar M.S M.J M.N M.F
      M.nOpen M.nDir M.fOpen M.fDir M.e M.v M.eValue M.cG M.hcG M.fieldCocone M.hb M.m₀
        (@prefix_coordinate_square.{u} K hK hAlg hChar G word M) G word (𝟙 (bsdhScheme G word))
        (Category.id_comp (bsdhToSpec G word))
      M.point M.a M.ha M.beta M.hgroup (@section_character_laws.{u,u} K hK hAlg hChar G M.J M.F
        M.beta M.hnatural M.hbeta).1 (@section_character_laws.{u,u} K hK hAlg hChar G M.J M.F M.beta
        M.hnatural M.hbeta).2 M.delta M.hdelta M.hco M.hn i B hB
      Y0 hcompact base0 hsmooth z hz j0 hwhole start hstart
  obtain ⟨Tstage, hBT, hstartT, hTstage, hframes⟩ := hcoframes
  refine ⟨Tstage, hBT, hstartT, hTstage, ?_⟩
  intro YT hYT baseT hSmooth qT nT hbase hqT hnT n
  have hframeN := @hframes YT hYT baseT hSmooth qT nT hbase hqT hnT n
  obtain ⟨E, hE⟩ := hframeN
  refine ⟨E, ?_⟩
  have hvalue := @wordChartPreimage_section.{u} K hK hAlg hChar G M.J M.F M.fOpen M.fDir
    M.fieldCocone M.hb word (𝟙 (bsdhScheme G word)) M.point M.a M.ha M.beta M.hgroup
    (@section_character_laws.{u,u} K hK hAlg hChar G M.J M.F M.beta M.hnatural M.hbeta).1
    (@section_character_laws.{u,u} K hK hAlg hChar G M.J M.F M.beta M.hnatural M.hbeta).2 M.S
    (inferInstanceAs (CommRing M.S)) M.N M.nOpen M.nDir M.v M.delta M.hdelta M.cG M.hcG M.m₀
    (@prefix_coordinate_square.{u} K hK hAlg hChar G word M) M.hco M.hn M.hv M.P M.hCoefficient M.hr
    i n
  have hmapN : polynomialMap.hom
      ((Polynomial.C (w : B ⊗[S0] M0) * (Polynomial.X : Polynomial (B ⊗[S0] M0)) ^ 2) ^ n) =
      SchubertGeometry.DeterminantSection.oppositionChartPolynomial G i n := hpoly n
  have hsectionField := @section_map K hK
  have hsectionSource := @hsectionField polynomialSource
  have hsectionMap0 := @hsectionSource polynomialTarget
  have hsectionMap1 := @hsectionMap0 polynomialMap
  have hsectionMap2 := @hsectionMap1 (inferInstanceAs (Algebra K (Polynomial
    (SchubertGeometry.DeterminantSection.chartAlgebra G i))))
  have hsectionMap3 := @hsectionMap2 (inferInstanceAs (IsReduced (Polynomial
    (SchubertGeometry.DeterminantSection.chartAlgebra G i))))
  have hsectionMap4 := @hsectionMap3 (inferInstanceAs (Algebra.FiniteType K (Polynomial
    (SchubertGeometry.DeterminantSection.chartAlgebra G i))))
  have hsectionMap5 := @hsectionMap4
    ((Polynomial.C (w : B ⊗[S0] M0) * (Polynomial.X : Polynomial (B ⊗[S0] M0)) ^ 2) ^ n)
  have hsectionMap6 := @hsectionMap5
    (SchubertGeometry.DeterminantSection.oppositionChartPolynomial G i n)
  have hsectionMap7 := @hsectionMap6 hmapN
  have hsectionValue := @polynomial_section_value K hK hAlg hChar G i n
  have hsectionMap8 := @hsectionMap7
    (SchubertGeometry.RetainedCharacter.polynomialSection G i n)
  have hpolynomial := @hsectionMap8 hsectionValue
  have hcoefficient :
      (Spec.map polynomialMap).appTop.hom ((Scheme.ΓSpecIso polynomialSource).inv.hom ((Polynomial.C
        (w : B ⊗[S0] M0) * (Polynomial.X : Polynomial (B ⊗[S0] M0)) ^ 2) ^ n)) =
        SchubertGeometry.RetainedCharacter.polynomialSection G i n := hpolynomial
  exact @preimageSection_reflect.{u} Tstage K
    (inferInstanceAs (CommRing Tstage)) hK.toCommRing
    (inferInstanceAs (Algebra Tstage K))
    (show Function.Injective (algebraMap Tstage K) from Subtype.val_injective)
    YT Y0 (wordChartPreimage G word (𝟙 (bsdhScheme G word)) i) M.cG.pt.left M.fieldCocone.pt.left
    baseT (inferInstanceAs (Flat baseT))
    (SchubertGeometry.RetainedCharacter.preimageSnd G word (𝟙 (bsdhScheme G word)) i ≫
      M.fieldCocone.pt.hom) nT hnT
    qT z hbase j0 (SchubertGeometry.RetainedCharacter.preimageSnd G word (𝟙 (bsdhScheme G word)) i)
      M.m₀ hwhole
    (@matchingModule.{u} M.S M.J (inferInstanceAs (CommRing M.S)) M.N M.cG M.delta n)
    (@coefficientMatchingSection.{u} M.S M.J (inferInstanceAs (CommRing M.S)) M.N M.cG M.delta
      (fun j => (M.P (FrobeniusSplitting.RetainedCharacter.singletonIndex j)).coeff 2) M.hr n)
    E (@wordChartPreimageFrame.{u} K hK hAlg hChar G M.J M.F M.fOpen M.fDir M.fieldCocone M.hb
      word (𝟙 (bsdhScheme G word)) M.point M.a M.ha M.beta M.hgroup (@section_character_laws.{u,u} K
        hK hAlg hChar G M.J M.F M.beta M.hnatural M.hbeta).1 (@section_character_laws.{u,u} K hK
        hAlg hChar G M.J M.F M.beta M.hnatural M.hbeta).2 M.S (inferInstanceAs (CommRing M.S))
      M.N M.nOpen M.nDir M.v M.delta M.hdelta M.cG M.hcG M.m₀ (@prefix_coordinate_square.{u} K hK
        hAlg hChar G word M) M.hco M.hn i n) hE
    polynomialSource polynomialTarget polynomialMap b0
    (SchubertGeometry.RetainedCharacter.preimageFst G word (𝟙 (bsdhScheme G word)) i) hb0
    ((Scheme.ΓSpecIso polynomialSource).inv.hom
      ((Polynomial.C (w : B ⊗[S0] M0) * Polynomial.X ^ 2) ^ n))
    (SchubertGeometry.RetainedCharacter.polynomialSection G i n) hcoefficient
    ((SchubertGeometry.RetainedCharacter.preimageFst G word (𝟙 (bsdhScheme G word)) i).appTop
      (SchubertGeometry.RetainedCharacter.polynomialSection G i n)) rfl hvalue


end SchubertGeometry.RetainedCharacter
