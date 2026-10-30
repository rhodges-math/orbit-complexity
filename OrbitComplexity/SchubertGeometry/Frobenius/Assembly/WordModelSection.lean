import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCoordinateSquare
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCharacterIdentification
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientEvaluation
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.CoordinateDiagramOpens
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# The retained word line and determinant section on one coefficient model

The field coordinate cocone comes from the inverse images of the original
finite affine cover. Tensor presentations and coefficient enlargements are
subsequently carried with that cocone and the original geometric projection.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct CategoryTheory.MonObj

noncomputable section

universe u

namespace SchubertGeometry.RetainedCharacter

open private intersection_preimage
  from OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.FixedCoordinateCocone
open private openCocone openCocone_isColimit
  from OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.FixedCoordinateProjection
open private intersectionCoordinates_finite intersectionCoordinates_smooth
  from OrbitComplexity.FrobeniusSplitting.Normality.CoordinateDiagrams
open private section_character_laws
  from OrbitComplexity.SchubertGeometry.Normality.BottSamelson.ChosenBorelCharacter
open private map_stage
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent
open private coefficientStageResult indexedStageResult wordCoefficientData wordPolynomialData
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientEvaluation
open private singletonIndex singletonArrow
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private selectedFrame selectedIndex
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent
open private chartLift
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase

open private inverseOpenDiagram fieldSchemeDiagram from
  OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison

private def fieldCoordinateMap {S K : Type u} [CommRing S] [CommRing K]
    {Y X : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    (baseK : X ⟶ Spec (.of K)) (q : X ⟶ Y) {J : Type u} (U : J → Y.Opens) :
    ∀ s, (intersectionCoordinates base (intersectionOpens U)).obj s →+*
      ((intersectionCoordinates baseK (inverseOpenDiagram q (intersectionOpens U))).obj s) :=
  fun s => (q ∣_ (intersectionOpens U).obj (op s)).appTop.hom

private theorem inverseOpenDiagram_eq {Y X : Scheme.{u}} (q : X ⟶ Y)
    {I : Type u} (U : I → Y.Opens) :
    inverseOpenDiagram q (intersectionOpens U) = intersectionOpens (fun i => q ⁻¹ᵁ U i) :=
  CategoryTheory.Functor.ext (fun s => intersection_preimage q U s)
    (fun _ _ _ => Subsingleton.elim _ _)

private theorem inverseCoordinates_affine {S K : Type u} [CommRing S] [CommRing K]
    [Algebra S K] {Y X : Scheme.{u}}
    (base : Y ⟶ Spec (.of S)) [IsProper base]
    (baseK : X ⟶ Spec (.of K)) (q : X ⟶ Y)
    (h : IsPullback q baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    {I : Type u} (U : I → Y.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    ∀ s, IsAffine
      ((fieldSchemeDiagram baseK (inverseOpenDiagram q (intersectionOpens U))).obj s).left := by
  let : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from base]
    infer_instance⟩
  intro s
  let : IsAffine ((intersectionOpens U).obj s).toScheme :=
    intersectionOpens_affine U hU s
  exact IsAffine.of_isPullback
    ((isPullback_morphismRestrict q ((intersectionOpens U).obj s)).paste_vert h)

private def inverseOpenCocone {K : Type u} [CommRing K] {Y X : Scheme.{u}}
    (baseK : X ⟶ Spec (.of K)) (q : X ⟶ Y) {I : Type u} (U : I → Y.Opens) :
    Cocone (fieldSchemeDiagram baseK (inverseOpenDiagram q (intersectionOpens U))) :=
  Cocone.mk (Over.mk baseK)
    { app := fun s => Over.homMk (((inverseOpenDiagram q (intersectionOpens U)).obj s).ι) rfl
      naturality := by
        intro s t f
        ext1
        change X.homOfLE (leOfHom ((inverseOpenDiagram q (intersectionOpens U)).map f)) ≫
            ((inverseOpenDiagram q (intersectionOpens U)).obj t).ι =
          ((inverseOpenDiagram q (intersectionOpens U)).obj s).ι ≫ 𝟙 X
        rw [Scheme.homOfLE_ι, Category.comp_id] }

private def fieldCoordinateCocone {K : Type u} [CommRing K] {Y X : Scheme.{u}}
    (baseK : X ⟶ Spec (.of K)) (q : X ⟶ Y) {I : Type u} (U : I → Y.Opens)
    (hE : ∀ s, IsAffine
      ((fieldSchemeDiagram baseK (inverseOpenDiagram q (intersectionOpens U))).obj s).left) :
    Cocone ((intersectionCoordinates baseK (inverseOpenDiagram q (intersectionOpens U))).op ⋙
        algSpec (.of K)) := by
  let : ∀ s, IsAffine
      ((fieldSchemeDiagram baseK (inverseOpenDiagram q (intersectionOpens U))).obj s).left := hE
  exact (Cocone.precompose
    (coordinateDiagramIso (.of K)
      (fieldSchemeDiagram baseK (inverseOpenDiagram q (intersectionOpens U)))).inv).obj
        (inverseOpenCocone baseK q U)

private def fieldCoordinateCocone_colimit {K : Type u} [CommRing K]
    {Y X : Scheme.{u}} (baseK : X ⟶ Spec (.of K)) (q : X ⟶ Y)
    {I : Type u} (U : I → Y.Opens) (hcover : (⨆ i, U i) = ⊤)
    (hE : ∀ s, IsAffine
      ((fieldSchemeDiagram baseK (inverseOpenDiagram q (intersectionOpens U))).obj s).left) :
    IsColimit (fieldCoordinateCocone baseK q U hE) := by
  let V := inverseOpenDiagram q (intersectionOpens U)
  let O := fun i => q ⁻¹ᵁ U i
  let E := fieldSchemeDiagram baseK V
  let : ∀ s, IsAffine (E.obj s).left := hE
  have hV : V = intersectionOpens O := inverseOpenDiagram_eq q U
  have hO : (⨆ i, O i) = ⊤ :=
    (TopologicalSpace.Opens.map_iSup q.base U).symm.trans
      ((congrArg (fun V : Y.Opens => q ⁻¹ᵁ V) hcover).trans
        (TopologicalSpace.Opens.map_top q.base))
  have hc₀ : IsColimit
      ((Over.forget (Spec (.of K))).mapCocone (inverseOpenCocone baseK q U)) := by
    change IsColimit (openCocone X V)
    exact openCocone_isColimit V O hV hO
  have hc : IsColimit (inverseOpenCocone baseK q U) :=
    isColimitOfReflects (Over.forget (Spec (.of K))) hc₀
  exact (IsColimit.precomposeInvEquiv (coordinateDiagramIso (.of K) E) _).symm hc

private theorem fieldCoordinateCocone_leg {K : Type u} [CommRing K]
    {Y X : Scheme.{u}} (baseK : X ⟶ Spec (.of K)) (q : X ⟶ Y)
    {I : Type u} (U : I → Y.Opens)
    (hE : ∀ s, IsAffine
      ((fieldSchemeDiagram baseK (inverseOpenDiagram q (intersectionOpens U))).obj s).left)
    (s : {s : Finset I // s.Nonempty}ᵒᵖ) :
    letI := hE
    ((fieldCoordinateCocone baseK q U hE).ι.app s).left =
      ((coordinateDiagramIso (.of K)
        (fieldSchemeDiagram baseK (inverseOpenDiagram q (intersectionOpens U)))).inv.app s).left ≫
          ((inverseOpenDiagram q (intersectionOpens U)).obj s).ι := rfl

private theorem fieldCoordinateDiagram_opens {S K : Type u} [CommRing S] [CommRing K]
    [Algebra S K] {Y X : Scheme.{u}} [X.IsSeparated]
    (base : Y ⟶ Spec (.of S)) (baseK : X ⟶ Spec (.of K)) (q : X ⟶ Y)
    (h : IsPullback q baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    {I : Type u} (U : I → Y.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    let F := intersectionCoordinates baseK (inverseOpenDiagram q (intersectionOpens U))
    (∀ (s t) (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))) ∧
    ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected := by
  let O := fun i => q ⁻¹ᵁ U i
  have hO (i : I) : IsAffineOpen (O i) := by
    let : IsAffine (U i).toScheme := hU i
    exact IsAffine.of_isPullback ((isPullback_morphismRestrict q (U i)).paste_vert h)
  let F := intersectionCoordinates baseK (inverseOpenDiagram q (intersectionOpens U))
  have hF : F = intersectionCoordinates baseK (intersectionOpens O) :=
    congrArg
      (intersectionCoordinates baseK)
      (inverseOpenDiagram_eq q U)
  exact coordinate_diagram_opens baseK O hO F (eqToIso hF)

private abbrev coordinateScalarScheme {S R : Type u} [CommRing S] [CommRing R]
    [Algebra S R] {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S)) : Scheme.{u} :=
  pullback base (Spec.map (CommRingCat.ofHom (algebraMap S R)))

private abbrev coordinateScalarBase {S R : Type u} [CommRing S] [CommRing R]
    [Algebra S R] {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S)) :
    coordinateScalarScheme (R := R) base ⟶ Spec (.of R) :=
  pullback.snd base (Spec.map (CommRingCat.ofHom (algebraMap S R)))

private abbrev coordinateScalarMap {S R : Type u} [CommRing S] [CommRing R]
    [Algebra S R] {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S)) :
    coordinateScalarScheme (R := R) base ⟶ Y :=
  pullback.fst base (Spec.map (CommRingCat.ofHom (algebraMap S R)))

private theorem retainedCoordinate_opens {S T R : Type u}
    [CommRing S] [CommRing T] [CommRing R]
    [Algebra S T] [Algebra T R] [Algebra S R] [IsScalarTower S T R]
    {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S)) [IsProper base]
    {I : Type u} (U : I → Y.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    let M := intersectionCoordinates base (intersectionOpens U)
    let qR := coordinateScalarMap (R := R) base
    let baseR := coordinateScalarBase (R := R) base
    let CR := intersectionCoordinates baseR (inverseOpenDiagram qR (intersectionOpens U))
    let N := fixedFibreDiagram (R := R) (M := R)
      (fixedFibreDiagram (R := T) (M := T) M)
    ∀ _d : fixedFibreDiagram (R := R) (M := R) M ≅ CR,
      (∀ (s t) (f : s ⟶ t), IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))) ∧
      ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
        Scheme.forget).IsLocallyDirected := by
  intro M qR baseR CR N d
  let : (coordinateScalarScheme (R := R) base).IsSeparated := ⟨by
    rw [← terminal.comp_from baseR]
    infer_instance⟩
  let O := fun i => qR ⁻¹ᵁ U i
  have hO (i : I) : IsAffineOpen (O i) := by
    let : IsAffine (U i).toScheme := hU i
    exact IsAffine.of_isPullback
      ((isPullback_morphismRestrict qR (U i)).paste_vert
        (IsPullback.of_hasPullback base
          (Spec.map (CommRingCat.ofHom (algebraMap S R)))))
  have hCR : CR = intersectionCoordinates baseR (intersectionOpens O) :=
    congrArg
      (intersectionCoordinates baseR)
      (inverseOpenDiagram_eq qR U)
  exact coordinate_diagram_opens baseR O hO N
    (fixedFibreCancelIso (T := T) (R := R) M ≪≫ d ≪≫ eqToIso hCR)

private theorem bind_coordinate_data
    {A : Sort*} {B : A → Sort*} {C : ∀ a, B a → Sort*}
    {D : ∀ a b, C a b → Prop} {E : ∀ a b, C a b → Sort*}
    {P : ∀ a b c, E a b c → Prop} {Q : Prop}
    (h : ∃ a b c, D a b c ∧ ∃ e, P a b c e)
    (f : ∀ a b c, D a b c → ∀ e, P a b c e → Q) : Q := by
  obtain ⟨a, b, c, hd, e, hp⟩ := h
  exact f a b c hd e hp

private theorem retain_coefficients
    {V : Sort*} {D : V → Sort*} {P : ∀ v, D v → Sort*} {H FG : Prop}
    {Ev Inj : V → Prop} {Hd Co Nat : ∀ v, D v → Prop}
    {Poly Single Match : ∀ v d, P v d → Prop}
    {Q : ∀ v, Ev v → Inj v → ∀ d, Hd v d → Co v d → Nat v d →
      ∀ p, Poly v d p → Single v d p → Prop}
    (h : ∃ v, H ∧ FG ∧ Ev v ∧ Inj v ∧ ∃ d, Hd v d ∧ Co v d ∧ Nat v d ∧
      ∃ p, Poly v d p ∧ Single v d p ∧ Match v d p)
    (f : ∀ v hev hv d hd hco hn p hpoly hsingle, Match v d p →
      Q v hev hv d hd hco hn p hpoly hsingle) :
    H ∧ FG ∧ ∃ v hev hv d hd hco hn p hpoly hsingle,
      Match v d p ∧ Q v hev hv d hd hco hn p hpoly hsingle := by
  obtain ⟨v, hH, hFG, hev, hv, d, hd, hco, hn, p, hpoly, hsingle, hmatch⟩ := h
  exact ⟨hH, hFG, v, hev, hv, d, hd, hco, hn, p, hpoly, hsingle, hmatch,
    f v hev hv d hd hco hn p hpoly hsingle hmatch⟩

private abbrev scalarSchemeDiagram {S R : Type u} [CommRing S] [CommRing R]
    [Algebra S R] {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    {J : Type u} (U : J → Y.Opens) :
    {s : Finset J // s.Nonempty}ᵒᵖ ⥤ Over (Spec (.of R)) :=
  fieldSchemeDiagram (coordinateScalarBase (R := R) base)
    (inverseOpenDiagram (coordinateScalarMap (R := R) base) (intersectionOpens U))

private abbrev scalarCoordinateRings {S R : Type u} [CommRing S] [CommRing R]
    [Algebra S R] {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    {J : Type u} (U : J → Y.Opens) :
    {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R :=
  intersectionCoordinates (coordinateScalarBase (R := R) base)
    (inverseOpenDiagram (coordinateScalarMap (R := R) base) (intersectionOpens U))

private abbrev singleCoordinateRings {S R : Type u} [CommRing S] [CommRing R]
    [Algebra S R] {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    {J : Type u} (U : J → Y.Opens) :
    {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R :=
  fixedFibreDiagram (R := R) (M := R) (intersectionCoordinates base (intersectionOpens U))

private abbrev retainedCoordinateRings {S T R : Type u}
    [CommRing S] [CommRing T] [CommRing R] [Algebra S T] [Algebra T R]
    {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    {J : Type u} (U : J → Y.Opens) :
    {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R :=
  fixedFibreDiagram (R := R) (M := R)
    (fixedFibreDiagram (R := T) (M := T) (intersectionCoordinates base (intersectionOpens U)))

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
    (base : Y ⟶ Spec (.of S)) [baseProper : IsProper base]
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

private def stageSectionResult : Prop :=
  ∃ (c₀ : Cocone ((singleCoordinateRings (R := R) base U).op ⋙ algSpec (.of R))) (hpt₀ : c₀.pt =
      Over.mk (coordinateScalarBase (R := R) base)),
    let cN := retainedCoordinateCocone (T := T) (intersectionCoordinates base (intersectionOpens U))
        c₀
    ∃ _hcN : IsColimit cN,
      let qN := scalarModelProjection (retainedCoordinateRings (T := T) (R := R) base U)
          (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))) v cN cF hcF
      IsPullback qN cF.pt.hom cN.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      qN ≫ (eqToHom hpt₀).left ≫ (coordinateScalarMap (R := R) base) = (eqToHom hptF).left ≫ qK ∧
      ∀ n : ℕ, ∃ E :
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
              (CharacterLine.wordDeterminantModuleSection G n word)

include hFopen hFdir hK hU hcover he hev hcoN hnN in
private theorem close_word_stage
    (hEK : ∀ s, IsAffine ((fieldSchemeDiagram baseK (inverseOpenDiagram qK (intersectionOpens
        U))).obj s).left)
    (hlF : ∀ s,
      letI := hEK
      (cF.ι.app s ≫ eqToHom hptF).left =
        ((coordinateDiagramIso (.of K) (fieldSchemeDiagram baseK (inverseOpenDiagram qK
            (intersectionOpens U)))).inv.app s).left ≫
          ((inverseOpenDiagram qK (intersectionOpens U)).obj s).ι) :
    stageSectionResult G base baseK qK U cF hcF hptF word q point a ha beta
      hgroup hco hn v hv delta hd P hP := by
  exact bind_coordinate_data
    (exists_fixed_coordinate_projection (R := R) base U hU hcover)
    (fun hER d c₀ hd₀ hpt₀ hrest => by
      let : ∀ s, IsAffine ((scalarSchemeDiagram (R := R) base U).obj s).left := hER
      let : ∀ s, IsAffine ((fieldSchemeDiagram baseK (inverseOpenDiagram qK (intersectionOpens
          U))).obj s).left := hEK
      let hc₀ : IsColimit c₀ := hrest.1.some
      let hN := retainedCoordinate_opens (T := T) base U hU d
      let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
          (Spec.map (CommRingCat.ofHom ((retainedCoordinateRings (T := T) (R := R) base U).map
              f).hom.toRingHom)) :=
        fun {_ _} f => hN.1 _ _ f
      let : (((retainedCoordinateRings (T := T) (R := R) base U).op ⋙ algSpec (.of R) ⋙ Over.forget
          (Spec (.of R))) ⋙
          Scheme.forget).IsLocallyDirected := hN.2
      let cN := retainedCoordinateCocone (T := T) (intersectionCoordinates base (intersectionOpens
          U)) c₀
      let qN := scalarModelProjection (retainedCoordinateRings (T := T) (R := R) base U)
          (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))) v cN cF hcF
      have hs := @retainedCoordinateProjection.{u} K kField S T R
        (Fact.out : S ≤ T) (Fact.out : T ≤ R) Y X base baseProper
        baseK qK hK J U hU hER hEK d e c₀ hc₀ hpt₀ cF hcF hptF v
        hd₀ he hrest.2 hlF hev
      let hcN : IsColimit cN := hs.1.some
      let hqN := scalarModelProjection_node (retainedCoordinateRings (T := T) (R := R) base U)
          (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))) v cN cF hcF
      refine ⟨c₀, hpt₀, hcN, hs.2.1, hs.2.2, ?_⟩
      intro n
      exact ⟨retainedWordLineIso G (intersectionCoordinates baseK (inverseOpenDiagram qK
          (intersectionOpens U))) cF hcF word q point a ha beta hgroup hco hn
        (retainedCoordinateRings (T := T) (R := R) base U) v delta hd cN hcN qN hqN hcoN hnN n,
        retainedWordLineIso_section G (intersectionCoordinates baseK (inverseOpenDiagram qK
            (intersectionOpens U))) cF hcF word q point a ha beta hgroup hco hn
          (retainedCoordinateRings (T := T) (R := R) base U) v delta hd cN hcN qN hqN hcoN hnN hv P
              hP n⟩)

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

private def coefficientSectionResult (H FG : Prop) : Prop :=
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
    stageSectionResult G base baseK qK U cF hcF hptF word q point a ha beta
      hgroup hco hn v hv delta hd P hP

private def rawCoefficientResult (H FG : Prop) : Prop :=
  let MT := fixedFibreDiagram (R := T) (M := T) (intersectionCoordinates base (intersectionOpens U))
  let N := fixedFibreDiagram (R := R) (M := R) MT
  wordCoefficientData (R := R) MT (intersectionCoordinates baseK (inverseOpenDiagram qK
      (intersectionOpens U)))
    (@scalarDiagramComparison.{u,u,u} K kField S T (Fact.out : S ≤ T)
      {s : Finset J // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty}))
      (intersectionCoordinates base (intersectionOpens U)) (intersectionCoordinates baseK
          (inverseOpenDiagram qK (intersectionOpens U))) e) H FG (wordTransitionUnit G
          (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))) beta)
    (wordRingCoefficient G (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
        U))) point a) (wordPolynomialData G (intersectionCoordinates baseK (inverseOpenDiagram qK
        (intersectionOpens U))) point a i N)

include hFopen hFdir in
private theorem close_coefficient_stage
    (hK : IsPullback qK baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : (⨆ j, U j) = ⊤)
    (he : ∀ s k x, e s (k ⊗ₜ[S] x) =
      algebraMap K ((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
          U))).obj s) k * fieldCoordinateMap base baseK qK U s x)
    (hEK : ∀ s, IsAffine
      ((fieldSchemeDiagram baseK (inverseOpenDiagram qK (intersectionOpens U))).obj s).left)
    (hlF : ∀ s,
      letI := hEK
      (cF.ι.app s ≫ eqToHom hptF).left =
        ((coordinateDiagramIso (.of K)
          (fieldSchemeDiagram baseK (inverseOpenDiagram qK (intersectionOpens U)))).inv.app s).left
              ≫
          ((inverseOpenDiagram qK (intersectionOpens U)).obj s).ι)
    (H FG : Prop)
    (h : rawCoefficientResult (S := S) (T := T) (R := R)
      (G := G) (base := base) (baseK := baseK) (qK := qK) (U := U)
      (point := point) (a := a) (beta := beta) (i := i) (e := e) H FG) :
    coefficientSectionResult (S := S) (T := T) (R := R)
      (G := G) (base := base) (baseK := baseK) (qK := qK) (U := U)
      (cF := cF) (hcF := hcF) (hptF := hptF) (word := word) (q := q)
      (point := point) (a := a) (ha := ha) (beta := beta) (hgroup := hgroup)
      (hco := hco) (hn := hn) (i := i) (e := e) H FG := by
  exact retain_coefficients
    (Q := fun v _ hv delta hd _ _ P _ hP =>
      stageSectionResult G base baseK qK U cF hcF hptF word q point a ha beta
        hgroup hco hn v hv delta hd P hP)
    h (fun v hev hv delta hd hcoN hnN P _ hP _ =>
      close_word_stage
        (S := S) (T := T) (R := R) (K := K)
        (G := G) (base := base) (baseK := baseK) (qK := qK) (hK := hK)
        (U := U) (hU := hU) (hcover := hcover)
        (cF := cF) (hcF := hcF) (hptF := hptF) (word := word) (q := q)
        (point := point) (a := a) (ha := ha) (beta := beta) (hgroup := hgroup)
        (hco := hco) (hn := hn) (e := e) (he := he) (v := v) (hev := hev)
        (hv := hv) (delta := delta) (hd := hd) (hcoN := hcoN) (hnN := hnN)
        (P := P) (hP := hP) (hEK := hEK) (hlF := hlF))

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

private def retainedStageResult (T : Subalgebra ℤ K) (hST : S ≤ T)
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
  coefficientSectionResult (S := S) (T := T) (R := R)
    (G := G) (base := base) (baseK := baseK) (qK := qK) (U := U)
    (cF := cF) (hcF := hcF) (hptF := hptF) (word := word) (q := q)
    (point := point) (a := a) (ha := ha) (beta := beta) (hgroup := hgroup)
    (hco := hco) (hn := hn) (i := i) (e := e) T.FG R.FG

include hFopen hFdir in
private theorem complete_subalgebra_stage
    (hK : IsPullback qK baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : (⨆ j, U j) = ⊤)
    (heval : ∀ s k x, e s (k ⊗ₜ[S] x) =
      algebraMap K ((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
          U))).obj s) k * fieldCoordinateMap base baseK qK U s x)
    (hEK : ∀ s, IsAffine
      ((fieldSchemeDiagram baseK (inverseOpenDiagram qK (intersectionOpens U))).obj s).left)
    (hlF : ∀ s,
      letI := hEK
      (cF.ι.app s ≫ eqToHom hptF).left =
        ((coordinateDiagramIso (.of K)
          (fieldSchemeDiagram baseK (inverseOpenDiagram qK (intersectionOpens U)))).inv.app s).left
              ≫
          ((inverseOpenDiagram qK (intersectionOpens U)).obj s).ι)
    (T : Subalgebra ℤ K) (hST : S ≤ T) (R : Subalgebra ℤ K) (hTR : T ≤ R)
    (h : coefficientStageResult G (intersectionCoordinates baseK (inverseOpenDiagram qK
        (intersectionOpens U))) point a beta i S (intersectionCoordinates base (intersectionOpens
        U)) e T hST R hTR) :
    retainedStageResult G S base baseK qK U cF hcF hptF word q point a ha beta
      hgroup hco hn i e T hST R hTR := by
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
  exact close_coefficient_stage
    (S := S) (T := T) (R := R) (K := K)
    (G := G) (base := base) (baseK := baseK) (qK := qK) (U := U)
    (cF := cF) (hcF := hcF) (hptF := hptF) (word := word) (q := q)
    (point := point) (a := a) (ha := ha) (beta := beta) (hgroup := hgroup)
    (hco := hco) (hn := hn) (i := i) (e := e) (hK := hK)
    (hU := hU) (hcover := hcover) (he := heval) (hEK := hEK) (hlF := hlF)
    (H := T.FG) (FG := R.FG) (h := h)

include hFopen hFdir in
private theorem exists_complete_coefficients [Finite J]
    (hS : S.FG)
    [∀ s, Algebra.FinitePresentation S ((intersectionCoordinates base (intersectionOpens U)).obj s)]
    [∀ s, Algebra.Smooth S ((intersectionCoordinates base (intersectionOpens U)).obj s)]
    (hK : IsPullback qK baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : (⨆ j, U j) = ⊤)
    (heval : ∀ s k x, e s (k ⊗ₜ[S] x) =
      algebraMap K ((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
          U))).obj s) k * fieldCoordinateMap base baseK qK U s x)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K ((intersectionCoordinates base (intersectionOpens
            U)).map f).hom) =
      ((intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))).map f).hom.comp
          (e s).toAlgHom)
    (hEK : ∀ s, IsAffine
      ((fieldSchemeDiagram baseK (inverseOpenDiagram qK (intersectionOpens U))).obj s).left)
    (hlF : ∀ s,
      letI := hEK
      (cF.ι.app s ≫ eqToHom hptF).left =
        ((coordinateDiagramIso (.of K)
          (fieldSchemeDiagram baseK (inverseOpenDiagram qK (intersectionOpens U)))).inv.app s).left
              ≫
          ((inverseOpenDiagram qK (intersectionOpens U)).obj s).ι)
    (hnatural : ∀ s t (f : s ⟶ t) j hj k hk,
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map ((intersectionCoordinates baseK (inverseOpenDiagram qK
            (intersectionOpens U))).map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T) (R : Subalgebra ℤ K) (hTR : T ≤ R),
      retainedStageResult G S base baseK qK U cF hcF hptF word q point a ha beta
        hgroup hco hn i e T hST R hTR := by
  have hcoeff : ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      indexedStageResult G (intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens
          U))) point a beta i S (intersectionCoordinates base (intersectionOpens U)) e T hST :=
    exists_word_coefficient_evaluation
      (K := K) (J := J) (G := G) (F := (intersectionCoordinates baseK (inverseOpenDiagram qK
          (intersectionOpens U)))) (hopen := hFopen) (hdir := hFdir)
      (cF := cF) (hcF := hcF) (word := word) (q := q)
      (point := point) (a := a) (ha := ha) (beta := beta)
      (hgroup := hgroup) (hco := hco) (hn := hn)
      (i := i) (S := S) (hS := hS) (M := (intersectionCoordinates base (intersectionOpens U))) (e :=
          e) (he := he)
      (hnatural := hnatural) (hbeta := hbeta)
  exact map_stage
    (P := indexedStageResult G (intersectionCoordinates baseK (inverseOpenDiagram qK
        (intersectionOpens U))) point a beta i S (intersectionCoordinates base (intersectionOpens
        U)) e)
    (Q := fun T hST => ∃ (R : Subalgebra ℤ K) (hTR : T ≤ R),
      retainedStageResult G S base baseK qK U cF hcF hptF word q point a ha beta
        hgroup hco hn i e T hST R hTR)
    hcoeff (fun T hST hT =>
      map_stage
        (P := coefficientStageResult G (intersectionCoordinates baseK (inverseOpenDiagram qK
            (intersectionOpens U))) point a beta i S (intersectionCoordinates base
            (intersectionOpens U)) e T hST)
        (Q := retainedStageResult G S base baseK qK U cF hcF hptF word q point a ha beta
          hgroup hco hn i e T hST)
        hT (fun R hTR hR =>
          complete_subalgebra_stage
            (K := K) (G := G) (S := S) (base := base) (baseK := baseK) (qK := qK)
            (U := U) (cF := cF) (hcF := hcF) (hptF := hptF) (word := word) (q := q)
            (point := point) (a := a) (ha := ha) (beta := beta) (hgroup := hgroup)
            (hco := hco) (hn := hn) (i := i) (e := e)
            (hK := hK) (hU := hU) (hcover := hcover) (heval := heval)
            (hEK := hEK) (hlF := hlF) (T := T) (hST := hST)
            (R := R) (hTR := hTR) (h := hR)))

end Retained

private theorem map_prior_coordinates {E : Sort*} {Ev Nat Q : E → Prop}
    (h : ∃ e, Ev e ∧ Nat e) (f : ∀ e, Ev e → Nat e → Q e) :
    ∃ e, Ev e ∧ Nat e ∧ Q e := by
  obtain ⟨e, hev, hn⟩ := h
  exact ⟨e, hev, hn, f e hev hn⟩

private theorem exists_retained_model_data
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (S : Subalgebra ℤ K) (hS : S.FG)
    {Y X : Scheme.{u}} [X.IsSeparated]
    (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base]
    (baseK : X ⟶ Spec (.of K)) (qK : X ⟶ Y)
    (hK : IsPullback qK baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    {J : Type u} [Finite J] (U : J → Y.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : (⨆ j, U j) = ⊤)
    (word : List G.rootBase.support) (i : G.rootBase.support) :
    let M := intersectionCoordinates base (intersectionOpens U)
    let F := intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))
    let hEK := inverseCoordinates_affine base baseK qK hK U hU
    let cF := fieldCoordinateCocone baseK qK U hEK
    let hcF := fieldCoordinateCocone_colimit baseK qK U hcover hEK
    ∀ (q : cF.pt.left ⟶ bsdhScheme G word) (point : J → G.points)
      (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
        (oppositeUnipotentVariety G).toOver)
      (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
        (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
      (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
        (k : J) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
      (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
        chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
      (hnatural : ∀ s t (f : s ⟶ t) j hj k hk,
        beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
          (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
      (hbeta : ∀ s j hj k hk l hl,
        beta s j hj l hl = beta s k hk l hl * beta s j hj k hk),
      let hF := fieldCoordinateDiagram_opens base baseK qK hK U hU
      letI : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
          (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)) :=
        fun {_ _} f => hF.1 _ _ f
      letI : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
        Scheme.forget).IsLocallyDirected := hF.2
      let laws := section_character_laws G F beta hnatural hbeta
      ∃ e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s,
        (∀ s k x, e s (k ⊗ₜ[S] x) =
          algebraMap K (F.obj s) k * fieldCoordinateMap base baseK qK U s x) ∧
        (∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
            (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
          (F.map f).hom.comp (e s).toAlgHom) ∧
        ∃ (T : Subalgebra ℤ K) (hST : S ≤ T) (R : Subalgebra ℤ K) (hTR : T ≤ R),
          retainedStageResult G S base baseK qK U cF hcF rfl word q point a ha beta
            hgroup laws.1 laws.2 i e T hST R hTR := by
  intro M F hEK cF hcF q point a ha beta hgroup hnatural hbeta hF
  let laws := section_character_laws G F beta hnatural hbeta
  let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)) := fun {_ _} f => hF.1 _ _ f
  let : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected := hF.2
  change ∃ e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s,
    (∀ s k x, e s (k ⊗ₜ[S] x) =
      algebraMap K (F.obj s) k * fieldCoordinateMap base baseK qK U s x) ∧
    (∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
      (F.map f).hom.comp (e s).toAlgHom) ∧
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T) (R : Subalgebra ℤ K) (hTR : T ≤ R),
      retainedStageResult G S base baseK qK U cF hcF rfl word q point a ha beta
        hgroup laws.1 laws.2 i e T hST R hTR
  let : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from base]
    infer_instance⟩
  let : ∀ s, Algebra.FinitePresentation S (M.obj s) :=
    fun s => intersectionCoordinates_finite base U hU s
  let : ∀ s, Algebra.Smooth S (M.obj s) := fun s => by
    let : Smooth (((intersectionOpens U).obj (op s)).ι ≫ base) := inferInstance
    exact intersectionCoordinates_smooth base U hU s
  have hleg : ∀ s,
      letI := hEK
      (cF.ι.app s ≫ eqToHom (show cF.pt = Over.mk baseK from rfl)).left =
        ((coordinateDiagramIso (.of K)
          (fieldSchemeDiagram baseK (inverseOpenDiagram qK (intersectionOpens U)))).inv.app s).left
              ≫
          ((inverseOpenDiagram qK (intersectionOpens U)).obj s).ι := by
    intro s
    exact (congrArg
      (fun f : (F.op ⋙ algSpec (.of K)).obj s ⟶ cF.pt => f.left)
      (Category.comp_id (cF.ι.app s))).trans
        (fieldCoordinateCocone_leg baseK qK U hEK s)
  exact map_prior_coordinates
    (Q := fun e => ∃ (T : Subalgebra ℤ K) (hST : S ≤ T)
        (R : Subalgebra ℤ K) (hTR : T ≤ R),
      retainedStageResult G S base baseK qK U cF hcF rfl word q point a ha beta
        hgroup laws.1 laws.2 i e T hST R hTR)
    (prior_intersection_coordinates base baseK qK hK U hU)
    (fun e heval he =>
      exists_complete_coefficients
        (K := K) (J := J) (G := G) (S := S)
        (base := base) (baseK := baseK) (qK := qK) (U := U)
        (cF := cF) (hcF := hcF) (hptF := rfl) (word := word) (q := q)
        (point := point) (a := a) (ha := ha) (beta := beta) (hgroup := hgroup)
        (hco := laws.1) (hn := laws.2) (i := i) (e := e)
        (hS := hS) (hK := hK) (hU := hU) (hcover := hcover)
        (heval := heval) (he := he) (hEK := hEK) (hlF := hleg)
        (hnatural := hnatural) (hbeta := hbeta))

/-- One pair of coefficient extensions carries the full word character and
all determinant powers on the scalar extension of the original proper model.
Its field pullback identifies both the line and the section along the original
geometric scalar projection. -/
theorem exists_retained_word_model
    {K : Type u} [kField : Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (S : Subalgebra ℤ K) (hS : S.FG)
    {Y X : Scheme.{u}} [X.IsSeparated]
    (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base]
    (baseK : X ⟶ Spec (.of K)) (qK : X ⟶ Y)
    (hK : IsPullback qK baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    {J : Type u} [Finite J] (U : J → Y.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : (⨆ j, U j) = ⊤)
    (word : List G.rootBase.support) (i : G.rootBase.support) :
    let M := intersectionCoordinates base (intersectionOpens U)
    let F := intersectionCoordinates baseK (inverseOpenDiagram qK (intersectionOpens U))
    let hEK := inverseCoordinates_affine base baseK qK hK U hU
    let cF := fieldCoordinateCocone baseK qK U hEK
    let hcF := fieldCoordinateCocone_colimit baseK qK U hcover hEK
    ∀ (q : cF.pt.left ⟶ bsdhScheme G word) (point : J → G.points)
      (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
        (oppositeUnipotentVariety G).toOver)
      (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
        (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
      (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
        (k : J) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
      (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
        chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
      (hnatural : ∀ s t (f : s ⟶ t) j hj k hk,
        beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
          (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
      (hbeta : ∀ s j hj k hk l hl,
        beta s j hj l hl = beta s k hk l hl * beta s j hj k hk),
      let hF := fieldCoordinateDiagram_opens base baseK qK hK U hU
      letI : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
          (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom)) :=
        fun {_ _} f => hF.1 _ _ f
      letI : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
        Scheme.forget).IsLocallyDirected := hF.2
      let laws := section_character_laws G F beta hnatural hbeta
      ∃ e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s,
        (∀ s k x, e s (k ⊗ₜ[S] x) =
          algebraMap K (F.obj s) k * fieldCoordinateMap base baseK qK U s x) ∧
        (∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
            (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
          (F.map f).hom.comp (e s).toAlgHom) ∧
        ∃ (T : Subalgebra ℤ K) (hST : S ≤ T) (R : Subalgebra ℤ K) (hTR : T ≤ R),
          letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
          letI : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
          letI : Algebra T R := (Subalgebra.inclusion hTR).toAlgebra
          letI : IsScalarTower T R K := Subalgebra.inclusion.isScalarTower_right hTR K
          letI : Algebra S R := (Subalgebra.inclusion (hST.trans hTR)).toAlgebra
          letI : IsScalarTower S R K :=
            Subalgebra.inclusion.isScalarTower_right (hST.trans hTR) K
          letI : IsScalarTower S T R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
          let sr := Spec.map (CommRingCat.ofHom (algebraMap S R))
          let qR := pullback.fst base sr
          let baseR := pullback.snd base sr
          let N₀ := fixedFibreDiagram (R := R) (M := R) M
          let MT := fixedFibreDiagram (R := T) (M := T) M
          let N := fixedFibreDiagram (R := R) (M := R) MT
          T.FG ∧ R.FG ∧
          ∃ (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
                F ⋙ forget₂ (CommAlgCat K) CommRingCat)
            (_hev : ∀ s x, (v.app s).hom x =
              (@scalarDiagramComparison.{u,u,u} K kField S T hST
                {s : Finset J // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset J // s.Nonempty}))
                M F e s)
                (Algebra.TensorProduct.map (IsScalarTower.toAlgHom T R K)
                  (AlgHom.id T (MT.obj s)) x))
            (hv : ∀ s, Function.Injective (v.app s).hom)
            (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
              (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
            (hd : ∀ s j hj k hk, (v.app s).hom (delta s j hj k hk : N.obj s) =
              (wordTransitionUnit G F beta s j hj k hk : F.obj s))
            (_hcoN : ∀ s j hj k hk l hl,
              delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
            (_hnN : ∀ s t (f : s ⟶ t) j hj k hk,
              Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
                delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
            (P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s))
            (_hpoly : ∀ s, (P s).natDegree ≤ 2 ∧
              Polynomial.map (v.app s).hom (P s) =
                Polynomial.map (Spec.preimage (selectedFrame G F a s ≫
                  flagChartMap G (point (selectedIndex s))).left).hom
                    (DeterminantSection.simpleFramePolynomial G i
                      (DeterminantSection.positiveDetCoefficient G)) ∧
              (v.app s).hom ((P s).coeff 2) =
                (Spec.preimage (selectedFrame G F a s ≫
                  flagChartMap G (point (selectedIndex s))).left).hom
                    (DeterminantSection.positiveDetCoefficient G) ∧
              ∀ n : ℕ, ((P s) ^ n).coeff (2 * n) = ((P s).coeff 2) ^ n)
            (hP : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
              wordRingCoefficient G F point a j),
            (∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
              (N.map (singletonArrow s j hj)).hom ((P (singletonIndex j)).coeff 2) =
                (N.map (singletonArrow s k hk)).hom ((P (singletonIndex k)).coeff 2) *
                  (delta s j hj k hk : N.obj s)) ∧
            ∃ (c₀ : Cocone (N₀.op ⋙ algSpec (.of R))) (hpt₀ : c₀.pt = Over.mk baseR),
              let cN := retainedCoordinateCocone (T := T) M c₀
              ∃ _hcN : IsColimit cN,
                let qN := scalarModelProjection N F v cN cF hcF
                IsPullback qN cF.pt.hom cN.pt.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
                qN ≫ (eqToHom hpt₀).left ≫ qR = (eqToHom (show cF.pt = Over.mk baseK from rfl)).left
                    ≫ qK ∧
                ∀ n : ℕ, ∃ E :
                    (Scheme.Modules.pullback qN).obj (matchingModule N cN delta n) ≅
                      (Scheme.Modules.pullback q).obj
                        (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word),
                  (Scheme.Modules.pullbackObjUnitIso qN).inv ≫
                      (Scheme.Modules.pullback qN).map
                        (retainedWordSection G F cF hcF word q point a ha beta hgroup laws.1 laws.2
                          N v hv delta hd P hP cN n) ≫ E.hom =
                    (Scheme.Modules.pullbackObjUnitIso q).inv ≫
                      (Scheme.Modules.pullback q).map
                        (CharacterLine.wordDeterminantModuleSection G n word) := by
  exact exists_retained_model_data
    (K := K) (G := G) (S := S) (hS := hS)
    (Y := Y) (X := X) (base := base) (baseK := baseK) (qK := qK) (hK := hK)
    (J := J) (U := U) (hU := hU) (hcover := hcover) (word := word) (i := i)

end SchubertGeometry.RetainedCharacter
