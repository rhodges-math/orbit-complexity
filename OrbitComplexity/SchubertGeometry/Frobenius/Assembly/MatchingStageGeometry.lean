import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoverModels
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Append atlas and matching-cover comparisons

The coefficient, atlas and character witnesses are kept together while the
polynomial cover is extended to the matching model. Its common affine charts
retain the smooth structure maps and their field tensor comparisons.
-/

set_option autoImplicit false
set_option pp.maxSteps 1000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

namespace SchubertGeometry

open RetainedCharacter

universe u

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private coordinateScalarBase coordinateScalarMap
  fieldCoordinateCocone fieldCoordinateCocone_colimit
  fieldCoordinateDiagram_opens fieldCoordinateMap inverseCoordinates_affine
  retainedCoordinateRings retainedCoordinate_opens coefficientSectionResult
  retainedStageResult stageSectionResult singleCoordinateRings from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordModelSection
open private inverseOpenDiagram from
  OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison
open private wordSchemeSeparated from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoverModels
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private selectedFrame selectedIndex from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent
open private map_exists_witness from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendWordModel

private theorem polynomial_chart_structure {S A : Type u}
    [CommRing S] [CommRing A] [Algebra S A] {X Y : Scheme.{u}}
    (f : Spec (.of (Polynomial A)) ⟶ X) (q : X ⟶ Y)
    (base : Y ⟶ Spec (.of S)) (j : Spec (.of A) ⟶ Y)
    (hf : f ≫ q = Spec.map (CommRingCat.ofHom
      (Polynomial.C : A →+* Polynomial A)) ≫ j)
    (hj : j ≫ base = Spec.map (CommRingCat.ofHom (algebraMap S A))) :
    f ≫ (q ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial A))) := by
  calc
    f ≫ (q ≫ base) = (f ≫ q) ≫ base := (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ j) ≫
        base := congrArg (· ≫ base) hf
    _ = Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S A)) :=
      (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hj)
    _ = Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial A))) := by
      change Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap S A)) =
        Spec.map (CommRingCat.ofHom (algebraMap S A) ≫
          CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))
      exact (Spec.map_comp _ _).symm

section FieldCoordinates

/-- Tensor comparisons on a common affine cover after scalar extension. -/
private def matchingCommonField {R K : Type u}
    [CommRing R] [CommRing K] [Algebra R K]
    (_hR : Function.Injective (algebraMap R K))
    {Y Z : Scheme.{u}} [Y.IsSeparated]
    (base : Y ⟶ Spec (.of R))
    (baseK : Z ⟶ Spec (.of K)) (n : Z ⟶ Y)
    (_hK : IsPullback n baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (W V : Y.OpenCover.{u})
    [∀ j, IsAffine (W.X j)] [∀ j, IsAffine (V.X j)] : Prop :=
  let C := appendCommonCover W V
  Finite C.I₀ ∧ ∀ l : C.I₀,
    let P := pullback (C.f l) n
    let f := C.f l ≫ base
    let t := pullback.snd (C.f l) n ≫ baseK
    let q := pullback.fst (C.f l) n
    letI : IsAffine (C.X l) := inferInstance
    letI : IsAffine P := by
      let : IsAffineHom n := MorphismProperty.of_isPullback _hK.flip inferInstance
      infer_instance
    let : Algebra R Γ(C.X l, ⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
    let : Algebra K Γ(P, ⊤) :=
      (t.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∃ (a : Spec Γ(C.X l, ⊤) ⟶ W.X l.1)
      (kN : Spec Γ(C.X l, ⊤) ⟶ V.X l.2)
      (kF : Spec Γ(P, ⊤) ⟶ pullback (V.f l.2) n),
      IsOpenImmersion a ∧ IsOpenImmersion kN ∧
      a ≫ W.f l.1 = (C.X l).isoSpec.inv ≫ C.f l ∧
      kN ≫ V.f l.2 = (C.X l).isoSpec.inv ≫ C.f l ∧
      Spec.map q.appTop ≫ kN = kF ≫ pullback.fst (V.f l.2) n ∧
      kF ≫ pullback.snd (V.f l.2) n =
        P.isoSpec.inv ≫ pullback.snd (C.f l) n ∧
      Module.Flat R Γ(C.X l, ⊤) ∧ Function.Injective q.appTop.hom ∧
      ∃ e : K ⊗[R] Γ(C.X l, ⊤) ≃ₐ[K] Γ(P, ⊤),
        (∀ k, e (k ⊗ₜ[R] (1 : Γ(C.X l, ⊤))) = algebraMap K Γ(P, ⊤) k) ∧
        (∀ x, e ((1 : K) ⊗ₜ[R] x) = q.appTop.hom x) ∧
        ∀ k x, e (k ⊗ₜ[R] x) = algebraMap K Γ(P, ⊤) k * q.appTop.hom x

private theorem proper_source_separated {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] :
    X.IsSeparated := by
  exact ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩

end FieldCoordinates

section Coordinates

variable {S R K J : Type u} [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K] [Finite J]
    {Y Z : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    [hproperBase : IsProper base] [hsmoothBase : Smooth base]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (c : Cocone (N.op ⋙ algSpec (.of R))) (hc : IsColimit c)
    (E : c.pt ≅ Over.mk (coordinateScalarBase (R := R) base))
    (U : Y.OpenCover.{u}) [Finite U.I₀]
    (A : U.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (eU : ∀ j, U.X j ≅ Spec (.of (Polynomial (A j))))
    (hU : ∀ j, ((eU j).inv ≫ U.f j) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial (A j)))))
    (hR : Function.Injective (algebraMap R K))
    (baseK : Z ⟶ Spec (.of K)) (n : Z ⟶ c.pt.left)
    (hK : IsPullback n baseK c.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))

/-- Polynomial and singleton covers on a retained matching model. -/
def matchingModelCoordinates : Prop :=
  let W := matchingSingletonCover N c hc
  let q := E.hom.left ≫ coordinateScalarMap (R := R) base
  ∃ (hWfinite : Finite W.I₀) (hWaff : ∀ j, IsAffine (W.X j)),
    let : Finite W.I₀ := hWfinite
    let : ∀ j, IsAffine (W.X j) := hWaff
    IsPullback q c.pt.hom base
      (Spec.map (CommRingCat.ofHom (algebraMap S R))) ∧
    ∃ (hproper : IsProper c.pt.hom) (hsmooth : Smooth c.pt.hom)
      (hsep : c.pt.left.IsSeparated),
      let : IsProper c.pt.hom := hproper
      let : Smooth c.pt.hom := hsmooth
      let : c.pt.left.IsSeparated := hsep
      ∃ (V : c.pt.left.OpenCover.{u}) (hfinite : Finite V.I₀)
        (haff : ∀ j, IsAffine (V.X j)) (index : V.I₀ ≃ U.I₀)
        (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (R ⊗[S] A (index j))))),
        let : Finite V.I₀ := hfinite
        let : ∀ j, IsAffine (V.X j) := haff
        (∀ j, V.f j ≫ c.pt.hom = (eV j).hom ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap R (Polynomial (R ⊗[S] A (index j)))))) ∧
        (∀ j, V.f j ≫ q = (eV j).hom ≫
          Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
            (Algebra.TensorProduct.includeRight : A (index j) →ₐ[S]
              R ⊗[S] A (index j)).toRingHom)) ≫
                (eU (index j)).inv ≫ U.f (index j)) ∧
        (∀ l, Smooth ((appendCommonCover W V).f l ≫ c.pt.hom)) ∧
        matchingCommonField hR c.pt.hom baseK n hK W V

include hU hproperBase hsmoothBase in
/-- Construct the common affine charts on the prescribed matching model. -/
theorem matching_model_coordinates :
    matchingModelCoordinates base N c hc E U A eU hR baseK n hK := by
  let W := matchingSingletonCover N c hc
  let q := E.hom.left ≫ coordinateScalarMap (R := R) base
  obtain ⟨hWfinite, hWaff, hq, hproper, hsmooth, V, hfinite, haff, index, eV,
    hVbase, hVold, _hC⟩ := exists_matching_model_cover base N c hc E U A eU hU
  let : Finite W.I₀ := hWfinite
  let : ∀ j, IsAffine (W.X j) := hWaff
  let : Finite V.I₀ := hfinite
  let : ∀ j, IsAffine (V.X j) := haff
  let : IsProper c.pt.hom := hproper
  let : Smooth c.pt.hom := hsmooth
  let hsep := proper_source_separated c.pt.hom
  let : c.pt.left.IsSeparated := hsep
  let C := appendCommonCover W V
  have hCsm : ∀ l, Smooth (C.f l ≫ c.pt.hom) := fun l => by
    let : IsOpenImmersion (C.f l) := C.map_prop l
    infer_instance
  refine ⟨hWfinite, hWaff, hq, hproper, hsmooth, hsep, V, hfinite, haff, index,
    eV, hVbase, hVold, hCsm, ?_⟩
  exact exists_append_matching_coordinates hR c.pt.hom baseK n hK W V
    (fun j => pullback (V.f j) n)
    (fun j => pullback.fst (V.f j) n)
    (fun j => pullback.snd (V.f j) n)
    (fun j => IsPullback.of_hasPullback (V.f j) n)

end Coordinates


section ScalarStages

variable {K : Type u} [kField : Field K] [IsAlgClosed K] [CharZero K]
    {S T R : Subalgebra ℤ K}
    [Fact (S ≤ T)] [Fact (T ≤ R)] [Fact (S ≤ R)]

private local instance wordAlgST : Algebra S T :=
  (Subalgebra.inclusion (Fact.out : S ≤ T)).toAlgebra
private local instance wordAlgTR : Algebra T R :=
  (Subalgebra.inclusion (Fact.out : T ≤ R)).toAlgebra
private local instance wordAlgSR : Algebra S R :=
  (Subalgebra.inclusion (Fact.out : S ≤ R)).toAlgebra
private local instance wordTowerSTK : IsScalarTower S T K :=
  Subalgebra.inclusion.isScalarTower_right (Fact.out : S ≤ T) K
private local instance wordTowerTRK : IsScalarTower T R K :=
  Subalgebra.inclusion.isScalarTower_right (Fact.out : T ≤ R) K
private local instance wordTowerSRK : IsScalarTower S R K :=
  Subalgebra.inclusion.isScalarTower_right (Fact.out : S ≤ R) K
private local instance wordTowerSTR : IsScalarTower S T R :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

section Stage

variable (G : ReductiveGroupData K) {Y X : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base]
    (baseK : X ⟶ Spec (.of K)) (qK : X ⟶ Y)
    (hK : IsPullback qK baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    {J : Type u} (U : J → Y.Opens) (hU : ∀ j, IsAffineOpen (U j))
    (hcover : (⨆ j, U j) = ⊤)


variable
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((intersectionCoordinates baseK (inverseOpenDiagram qK
          (intersectionOpens U))).map f).hom.toRingHom))]
    [hFdir : (((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).op ⋙
        algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone ((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).op ⋙
        algSpec (.of K))) (hcF : IsColimit cF)
    (hptF : cF.pt = Over.mk baseK)
    (word : List G.rootBase.support) (q : cF.pt.left ⟶ bsdhScheme G word)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op ((intersectionCoordinates baseK (inverseOpenDiagram qK
        (intersectionOpens U))).obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op ((intersectionCoordinates baseK (inverseOpenDiagram qK
          (intersectionOpens U))).obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G (intersectionCoordinates baseK (inverseOpenDiagram qK
        (intersectionOpens U))) point a s j hj =
      chartLift G (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U)))
          point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G (intersectionCoordinates baseK
        (inverseOpenDiagram qK (intersectionOpens U))) beta s j hj l hl =
      wordTransitionUnit G (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
          U))) beta s k hk l hl * wordTransitionUnit G (intersectionCoordinates baseK
          (inverseOpenDiagram qK (intersectionOpens U))) beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map ((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).map
          f).hom.toMonoidHom (wordTransitionUnit G (intersectionCoordinates baseK
          (inverseOpenDiagram qK (intersectionOpens U))) beta s j hj k hk) =
        wordTransitionUnit G (intersectionCoordinates baseK (inverseOpenDiagram qK
            (intersectionOpens U))) beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (e : ∀ s, K ⊗[S] (intersectionCoordinates base (intersectionOpens U)).obj s ≃ₐ[K]
        (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).obj s)
    (he : ∀ s k x, e s (k ⊗ₜ[S] x) =
      algebraMap K ((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
          U))).obj s) k *
        fieldCoordinateMap base baseK qK U s x)
    (v : (retainedCoordinateRings (T := T) (R := R) base U) ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))) ⋙ forget₂
          (CommAlgCat K) CommRingCat)
    (hev : ∀ s x, (v.app s).hom x =
      (@scalarDiagramComparison.{u,u,u} K kField S T (Fact.out : S ≤ T)
        {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty}))
        (intersectionCoordinates base (intersectionOpens U)) (intersectionCoordinates baseK
            (inverseOpenDiagram qK (intersectionOpens U))) e s)
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
          (AlgHom.id T (T ⊗[S] (intersectionCoordinates base (intersectionOpens U)).obj s)) x))
    (hv : ∀ s, Function.Injective (v.app s).hom)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), ((retainedCoordinateRings (T := T) (R := R) base U).obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (delta s j hj k hk : (retainedCoordinateRings (T := T) (R :=
        R) base U).obj s) =
      (wordTransitionUnit G (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
          U))) beta s j hj k hk : (intersectionCoordinates baseK (inverseOpenDiagram qK
          (intersectionOpens U))).obj s))
    (hcoN : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map ((retainedCoordinateRings (T := T) (R := R) base U).map f).hom.toMonoidHom (delta s
          j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial ((retainedCoordinateRings (T := T) (R := R)
        base U).obj s))
    (hP : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
      wordRingCoefficient G (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
          U))) point a j)

/-- A retained word line and section together with polynomial-cover coordinates. -/
def matchingStageResult
    (V : Y.OpenCover.{u})
    (A : V.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (A j))))
    (hR : Function.Injective (algebraMap R K)) : Prop :=
  ∃ (hJ : Finite J) (hVfinite : Finite V.I₀) (hsm : Smooth base),
  let : Finite J := hJ
  let : Finite V.I₀ := hVfinite
  let : Smooth base := hsm
  ∃ (c₀ : Cocone ((singleCoordinateRings (R := R) base U).op ⋙ algSpec (.of R))) (hpt₀ : c₀.pt =
      Over.mk (coordinateScalarBase (R := R) base)),
    let cN := retainedCoordinateCocone (T := T) (intersectionCoordinates base (intersectionOpens U))
        c₀
    ∃ _hcN : IsColimit cN,
      let qN := scalarModelProjection (retainedCoordinateRings (T := T) (R := R) base U)
          (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))) v cN cF hcF
      ∃ hCart : IsPullback qN cF.pt.hom cN.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))),
      qN ≫ (eqToHom hpt₀).left ≫ (coordinateScalarMap (R := R) base) = (eqToHom hptF).left ≫ qK ∧
      (∀ n : ℕ, ∃ E :
          (Scheme.Modules.pullback qN).obj (matchingModule (retainedCoordinateRings (T := T) (R :=
              R) base U) cN delta n) ≅
            (Scheme.Modules.pullback q).obj
              (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word),
        (Scheme.Modules.pullbackObjUnitIso qN).inv ≫
            (Scheme.Modules.pullback qN).map
              (retainedWordSection G (intersectionCoordinates baseK (inverseOpenDiagram qK
                  (intersectionOpens U))) cF hcF word q point a ha beta hgroup hco hn
                (retainedCoordinateRings (T := T) (R := R) base U) v hv delta hd P hP cN n) ≫ E.hom
                    =
          (Scheme.Modules.pullbackObjUnitIso q).inv ≫
            (Scheme.Modules.pullback q).map
              (CharacterLine.wordDeterminantModuleSection G n word)) ∧
      ∃ (hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
          (Spec.map (CommRingCat.ofHom
            ((retainedCoordinateRings (T := T) (R := R) base U).map f).hom.toRingHom)))
        (hNdir : ((((retainedCoordinateRings (T := T) (R := R) base U).op ⋙
          algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
            Scheme.forget).IsLocallyDirected)),
        let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
            (Spec.map (CommRingCat.ofHom
              ((retainedCoordinateRings (T := T) (R := R) base U).map f).hom.toRingHom)) :=
          hNopen
        let : ((((retainedCoordinateRings (T := T) (R := R) base U).op ⋙
          algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
            Scheme.forget).IsLocallyDirected) := hNdir
        matchingModelCoordinates base
          (retainedCoordinateRings (T := T) (R := R) base U) cN _hcN
          (eqToIso hpt₀) V A eV hR cF.pt.hom qN hCart


variable (V : Y.OpenCover.{u}) [Finite V.I₀]
    (A : V.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (A j))))
    (hV : ∀ j, ((eV j).inv ≫ V.f j) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial (A j)))))
    (hR : Function.Injective (algebraMap R K))
    [Finite J] [Smooth base]

include hU hcover hV in
/-- Extend the prescribed word-section witnesses by their affine coordinates. -/
theorem matching_stage_geometry
    (h : stageSectionResult G base baseK qK U cF hcF hptF word q point a ha
      beta hgroup hco hn v hv delta hd P hP) :
    matchingStageResult G base baseK qK U cF hcF hptF word q point a ha
      beta hgroup hco hn v hv delta hd P hP V A eV hR := by
  obtain ⟨c₀, hpt₀, hcN, hCart, hproj, hsections⟩ := h
  obtain ⟨_hE, d, _c, _hd, _hrest⟩ :=
    exists_fixed_coordinate_projection (R := R) base U hU hcover
  have hN := retainedCoordinate_opens (T := T) base U hU d
  let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        ((retainedCoordinateRings (T := T) (R := R) base U).map f).hom.toRingHom)) :=
    fun {_ _} f => hN.1 _ _ f
  let : ((((retainedCoordinateRings (T := T) (R := R) base U).op ⋙
    algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected) := hN.2
  refine ⟨inferInstance, inferInstance, inferInstance,
    c₀, hpt₀, hcN, hCart, hproj, hsections,
    (fun {_ _} f => hN.1 _ _ f), hN.2, ?_⟩
  exact matching_model_coordinates base
    (retainedCoordinateRings (T := T) (R := R) base U)
    (retainedCoordinateCocone (T := T) (intersectionCoordinates base (intersectionOpens U)) c₀) hcN
    (eqToIso hpt₀) V A eV hV hR cF.pt.hom
    (scalarModelProjection (retainedCoordinateRings (T := T) (R := R) base U)
      (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))) v
      (retainedCoordinateCocone (T := T) (intersectionCoordinates base (intersectionOpens U)) c₀)
      cF hcF) hCart

end Stage


section Coefficients

variable (G : ReductiveGroupData K)
    {Y X : Scheme.{u}} (base : Y ⟶ Spec (.of S)) [IsProper base]
    (baseK : X ⟶ Spec (.of K)) (qK : X ⟶ Y)
    {J : Type u} (U : J → Y.Opens)


variable
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((intersectionCoordinates baseK (inverseOpenDiagram qK
          (intersectionOpens U))).map f).hom.toRingHom))]
    [hFdir : (((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).op ⋙
        algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone ((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).op ⋙
        algSpec (.of K))) (hcF : IsColimit cF)
    (hptF : cF.pt = Over.mk baseK)
    (word : List G.rootBase.support) (q : cF.pt.left ⟶ bsdhScheme G word)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op ((intersectionCoordinates baseK (inverseOpenDiagram qK
        (intersectionOpens U))).obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op ((intersectionCoordinates baseK (inverseOpenDiagram qK
          (intersectionOpens U))).obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G (intersectionCoordinates baseK (inverseOpenDiagram qK
        (intersectionOpens U))) point a s j hj =
      chartLift G (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U)))
          point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G (intersectionCoordinates baseK
        (inverseOpenDiagram qK (intersectionOpens U))) beta s j hj l hl =
      wordTransitionUnit G (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
          U))) beta s k hk l hl * wordTransitionUnit G (intersectionCoordinates baseK
          (inverseOpenDiagram qK (intersectionOpens U))) beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map ((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).map
          f).hom.toMonoidHom (wordTransitionUnit G (intersectionCoordinates baseK
          (inverseOpenDiagram qK (intersectionOpens U))) beta s j hj k hk) =
        wordTransitionUnit G (intersectionCoordinates baseK (inverseOpenDiagram qK
            (intersectionOpens U))) beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (i : G.rootBase.support)
    (e : ∀ s, K ⊗[S] (intersectionCoordinates base (intersectionOpens U)).obj s ≃ₐ[K]
        (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).obj s)

/-- Coefficients, word sections and common-cover coordinates on one model. -/
def matchingCoefficientResult
    (V : Y.OpenCover.{u})
    (A : V.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (A j))))
    (hR : Function.Injective (algebraMap R K)) (H FG : Prop) : Prop :=
  let MT := fixedFibreDiagram (R := T) (M := T) (intersectionCoordinates base (intersectionOpens U))
  let N := fixedFibreDiagram (R := R) (M := R) MT
  H ∧ FG ∧
  ∃ (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
        (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))) ⋙ forget₂
            (CommAlgCat K) CommRingCat)
    (_hev : ∀ s x, (v.app s).hom x =
      (@scalarDiagramComparison.{u,u,u} K kField S T (Fact.out : S ≤ T)
        {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty}))
        (intersectionCoordinates base (intersectionOpens U)) (intersectionCoordinates baseK
            (inverseOpenDiagram qK (intersectionOpens U))) e s)
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
          (AlgHom.id T (MT.obj s)) x))
    (hv : ∀ s, Function.Injective (v.app s).hom)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (delta s j hj k hk : N.obj s) =
      (wordTransitionUnit G (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
          U))) beta s j hj k hk : (intersectionCoordinates baseK (inverseOpenDiagram qK
          (intersectionOpens U))).obj s))
    (_hcoN : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (_hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s))
    (_hpoly : ∀ s, (P s).natDegree ≤ 2 ∧
      Polynomial.map (v.app s).hom (P s) =
        Polynomial.map (Spec.preimage (selectedFrame G (intersectionCoordinates baseK
            (inverseOpenDiagram qK (intersectionOpens U))) a s ≫
          flagChartMap G (point (selectedIndex s))).left).hom
            (DeterminantSection.simpleFramePolynomial G i
              (DeterminantSection.positiveDetCoefficient G)) ∧
      (v.app s).hom ((P s).coeff 2) =
        (Spec.preimage (selectedFrame G (intersectionCoordinates baseK (inverseOpenDiagram qK
            (intersectionOpens U))) a s ≫
          flagChartMap G (point (selectedIndex s))).left).hom
            (DeterminantSection.positiveDetCoefficient G) ∧
      ∀ n : ℕ, ((P s) ^ n).coeff (2 * n) = ((P s).coeff 2) ^ n)
    (hP : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
      wordRingCoefficient G (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
          U))) point a j),
    (∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom ((P (singletonIndex j)).coeff 2) =
        (N.map (singletonArrow s k hk)).hom ((P (singletonIndex k)).coeff 2) *
          (delta s j hj k hk : N.obj s)) ∧
    matchingStageResult G base baseK qK U cF hcF hptF word q point a ha beta
      hgroup hco hn v hv delta hd P hP V A eV hR

variable (hU : ∀ j, IsAffineOpen (U j)) (hcover : (⨆ j, U j) = ⊤)
    (V : Y.OpenCover.{u}) [Finite V.I₀]
    (A : V.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (A j))))
    (hV : ∀ j, ((eV j).inv ≫ V.f j) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial (A j)))))
    (hR : Function.Injective (algebraMap R K))
    [Finite J] [Smooth base]

include hU hcover hV in
/-- Keep every coefficient witness while adjoining its chart comparisons. -/
theorem matching_coefficient_geometry (H FG : Prop)
    (h : coefficientSectionResult (S := S) (T := T) (R := R)
      G base baseK qK U cF hcF hptF word q point a ha beta hgroup hco hn i e H FG) :
    matchingCoefficientResult (S := S) (T := T) (R := R)
      G base baseK qK U cF hcF hptF word q point a ha beta hgroup hco hn i e
      V A eV hR H FG := by
  obtain ⟨hH, hFG, v, hev, hv, delta, hd, hcoN, hnN, P, hpoly, hP, hr, hs⟩ := h
  refine ⟨hH, hFG, v, hev, hv, delta, hd, hcoN, hnN, P, hpoly, hP, hr, ?_⟩
  exact matching_stage_geometry G base baseK qK U hU hcover cF hcF hptF word q
    point a ha beta hgroup hco hn v hv delta hd P hP V A eV hV hR hs

end Coefficients

end ScalarStages


section Retained

variable {K : Type u} [kField : Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (S : Subalgebra ℤ K)
    {Y X : Scheme.{u}} (base : Y ⟶ Spec (.of S)) [IsProper base]
    (baseK : X ⟶ Spec (.of K)) (qK : X ⟶ Y)
    {J : Type u} (U : J → Y.Opens)


variable
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((intersectionCoordinates baseK (inverseOpenDiagram qK
          (intersectionOpens U))).map f).hom.toRingHom))]
    [hFdir : (((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).op ⋙
        algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone ((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).op ⋙
        algSpec (.of K))) (hcF : IsColimit cF)
    (hptF : cF.pt = Over.mk baseK)
    (word : List G.rootBase.support) (q : cF.pt.left ⟶ bsdhScheme G word)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op ((intersectionCoordinates baseK (inverseOpenDiagram qK
        (intersectionOpens U))).obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op ((intersectionCoordinates baseK (inverseOpenDiagram qK
          (intersectionOpens U))).obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G (intersectionCoordinates baseK (inverseOpenDiagram qK
        (intersectionOpens U))) point a s j hj =
      chartLift G (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U)))
          point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G (intersectionCoordinates baseK
        (inverseOpenDiagram qK (intersectionOpens U))) beta s j hj l hl =
      wordTransitionUnit G (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
          U))) beta s k hk l hl * wordTransitionUnit G (intersectionCoordinates baseK
          (inverseOpenDiagram qK (intersectionOpens U))) beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map ((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).map
          f).hom.toMonoidHom (wordTransitionUnit G (intersectionCoordinates baseK
          (inverseOpenDiagram qK (intersectionOpens U))) beta s j hj k hk) =
        wordTransitionUnit G (intersectionCoordinates baseK (inverseOpenDiagram qK
            (intersectionOpens U))) beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (i : G.rootBase.support)
    (e : ∀ s, K ⊗[S] (intersectionCoordinates base (intersectionOpens U)).obj s ≃ₐ[K]
        (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).obj s)

/-- A coefficient stage carrying the original line and its common affine cover. -/
def matchingRetainedResult
    (V : Y.OpenCover.{u})
    (A : V.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (A j))))
    (T : Subalgebra ℤ K) (hST : S ≤ T)
    (R : Subalgebra ℤ K) (hTR : T ≤ R) : Prop :=
  letI : Fact (S ≤ T) := ⟨hST⟩
  letI : Fact (T ≤ R) := ⟨hTR⟩
  letI : Fact (S ≤ R) := ⟨hST.trans hTR⟩
  letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  letI : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  letI : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  letI : IsScalarTower T R K := Subalgebra.inclusion.isScalarTower_right hTR K
  letI : Algebra S R := (Subalgebra.inclusion (hST.trans hTR)).toAlgebra
  letI : IsScalarTower S R K :=
    Subalgebra.inclusion.isScalarTower_right (hST.trans hTR) K
  letI : IsScalarTower S T R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  matchingCoefficientResult (S := S) (T := T) (R := R)
    (G := G) (base := base) (baseK := baseK) (qK := qK) (U := U)
    (cF := cF) (hcF := hcF) (hptF := hptF) (word := word) (q := q)
    (point := point) (a := a) (ha := ha) (beta := beta) (hgroup := hgroup)
    (hco := hco) (hn := hn) (i := i) (e := e) V A eV (show Function.Injective (algebraMap R K) from
        Subtype.val_injective) T.FG R.FG


variable (hU : ∀ j, IsAffineOpen (U j)) (hcover : (⨆ j, U j) = ⊤)
    (V : Y.OpenCover.{u}) [Finite V.I₀]
    (A : V.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (A j))))
    (hV : ∀ j, ((eV j).inv ≫ V.f j) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial (A j)))))
    [Finite J] [Smooth base]

include hU hcover hV in
/-- Apply the affine-coordinate construction with the given inclusion algebras. -/
theorem matching_retained_geometry (T : Subalgebra ℤ K) (hST : S ≤ T)
    (R : Subalgebra ℤ K) (hTR : T ≤ R)
    (h : retainedStageResult G S base baseK qK U cF hcF hptF word q point a ha
      beta hgroup hco hn i e T hST R hTR) :
    matchingRetainedResult G S base baseK qK U cF hcF hptF word q point a ha
      beta hgroup hco hn i e V A eV T hST R hTR := by
  let : Fact (S ≤ T) := ⟨hST⟩
  let : Fact (T ≤ R) := ⟨hTR⟩
  let : Fact (S ≤ R) := ⟨hST.trans hTR⟩
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
  let : IsScalarTower T R K := Subalgebra.inclusion.isScalarTower_right hTR K
  let : Algebra S R := (Subalgebra.inclusion (hST.trans hTR)).toAlgebra
  let : IsScalarTower S R K :=
    Subalgebra.inclusion.isScalarTower_right (hST.trans hTR) K
  let : IsScalarTower S T R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact matching_coefficient_geometry G base baseK qK U cF hcF hptF word q
    point a ha beta hgroup hco hn i e hU hcover V A eV hV
    (show Function.Injective (algebraMap R K) from Subtype.val_injective)
    T.FG R.FG h

end Retained

end SchubertGeometry
