import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierCharts
import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialIdeals
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChart
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPriorIdeals
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Ideals preserved by relative Cartier maps

Raw coefficient operators preserve ideals extended from the preceding
coefficient ring, in the specified polynomial coordinates.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private unitModule from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.FramedOperatorMaps
open private imageIn from
  OrbitComplexity.FrobeniusSplitting.Cartier.OpenOperators
open private twistedOverMap twistedOverMap_comp_apply from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

private theorem ring_comap_preserves
    {R S : Type*} [CommRing R] [CommRing S] {p : ℕ}
    (φ : FrobeniusLinearMap R p) (ψ : FrobeniusLinearMap S p) (f : R →+* S)
    (h : ∀ a, f (φ a) = ψ (f a)) (I : Ideal S)
    (hI : ∀ a ∈ I, ψ a ∈ I) :
    ∀ a ∈ I.comap f, φ a ∈ I.comap f := by
  intro a ha
  change f (φ a) ∈ I
  rw [h]
  exact hI _ ha

private theorem end_preserves {R : Type*} [CommRing R]
    (f : R →ₗ[R] R) (I : Ideal R) (a : R) (ha : a ∈ I) : f a ∈ I := by
  have h : f a = a * f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul a (1 : R)
  rw [h]
  exact I.mul_mem_right _ ha

private theorem spec_top_transport {R : Type u} [CommRing R] {p : ℕ}
    (φ : FrobeniusLinearMap R p) (hp : 0 < p) :
    ((φ.toSpec hp).onOpen ⊤).transport
      (StructureSheaf.globalSectionsIso R).symm.commRingCatIsoToRingEquiv = φ := by
  ext a
  change (StructureSheaf.globalSectionsIso R).inv
    ((φ.toSpec hp).onOpen ⊤ ((StructureSheaf.globalSectionsIso R).hom a)) = φ a
  have he (a : R) :
      (StructureSheaf.globalSectionsIso R).hom a =
        StructureSheaf.toOpenₗ R R ⊤ a := rfl
  have h : (φ.toSpec hp).onOpen ⊤ ((StructureSheaf.globalSectionsIso R).hom a) =
      (StructureSheaf.globalSectionsIso R).hom (φ a) :=
    (congrArg (fun b : Γ(Spec (.of R), ⊤) => (φ.toSpec hp).onOpen ⊤ b) (he a)).trans
      ((φ.toSpec_constant hp ⊤ a).trans (he (φ a)).symm)
  exact (congrArg (StructureSheaf.globalSectionsIso R).commRingCatIsoToRingEquiv.symm h).trans
    ((StructureSheaf.globalSectionsIso R).commRingCatIsoToRingEquiv.symm_apply_apply _)

private theorem pushforward_top_preserves {X Y : Scheme.{u}} {p : ℕ}
    (e : X ≅ Y) (φ : SchemeFrobeniusMap X p)
    (I : Ideal Γ(X, ⊤)) (hI : ∀ a ∈ I, φ.onOpen ⊤ a ∈ I) :
    ∀ a ∈ I.comap e.hom.appTop.hom,
      (φ.pushforward e.hom).onOpen ⊤ a ∈ I.comap e.hom.appTop.hom := by
  intro a ha
  change e.hom.appTop ((φ.pushforward e.hom).onOpen ⊤ a) ∈ I
  exact (φ.pushforward_app e.hom ⊤ a).symm ▸ hI _ ha

private theorem pullback_top_preserves {X Y : Scheme.{u}} {p : ℕ}
    (e : X ≅ Y) (φ : SchemeFrobeniusMap Y p)
    (I : Ideal Γ(X, ⊤))
    (hI : ∀ a ∈ I.comap e.hom.appTop.hom,
      φ.onOpen ⊤ a ∈ I.comap e.hom.appTop.hom) :
    ∀ a ∈ I, (φ.openPullback e.hom).onOpen ⊤ a ∈ I := by
  intro a ha
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.hom.op))
  obtain ⟨b, rfl⟩ := (asIso e.hom.appTop).commRingCatIsoToRingEquiv.surjective a
  change (φ.openPullback e.hom).onOpen ⊤ (e.hom.appTop b) ∈ I
  exact (φ.openPullback_natural e.hom ⊤ b).symm ▸ hI b ha

private theorem framed_top_preserves {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) (L : X.Modules) (U : X.Opens)
    (E : L.over U ≅ (unitModule X).over U)
    (H : (frobeniusRestriction C p base L).over U ⟶ (unitModule X).over U)
    (δ : L.over U ⟶ (unitModule X).over U)
    (τ : localOperators (sheafFrobenius C p base) U)
    (φ : SchemeFrobeniusMap U.toScheme p)
    (hτ : openOperatorEquiv C p base U τ = φ)
    (hH : ∀ (V : Over U) (m : L.val.obj (op V.left)),
      (H.val.app (op V)).hom m =
        (τ.val.app (op V)).hom ((δ.val.app (op V)).hom m))
    (I : Ideal Γ(U.toScheme, ⊤)) (hI : ∀ a ∈ I, φ.onOpen ⊤ a ∈ I) :
    ∀ a ∈ I, (framedOpenOperator base L U E H).onOpen ⊤ a ∈ I := by
  intro a ha
  let V : Over U := imageIn U ⊤
  let : CommRing ((Sheaf.over X.ringCatSheaf U).obj.obj (op V)) :=
    inferInstanceAs (CommRing Γ(X, V.left))
  let f := ((E.inv ≫ δ).val.app (op V)).hom
  have hf : f a ∈ I := end_preserves f I a ha
  have h₁ : (framedOpenOperator base L U E H).onOpen ⊤ a =
      ((twistedOverMap base (unitModule X) L U E.inv ≫ H).val.app (op V)).hom a :=
    openOperatorEquiv_apply C p base U _ ⊤ a
  have h₂ : ((twistedOverMap base (unitModule X) L U E.inv ≫ H).val.app (op V)).hom a =
      (H.val.app (op V)).hom ((E.inv.val.app (op V)).hom a) :=
    twistedOverMap_comp_apply base (unitModule X) L (unitModule X) U E.inv H V a
  have h₃ : (H.val.app (op V)).hom ((E.inv.val.app (op V)).hom a) =
      (τ.val.app (op V)).hom (f a) := hH V _
  have h₄ : (τ.val.app (op V)).hom (f a) = φ.onOpen ⊤ (f a) :=
    (openOperatorEquiv_apply C p base U τ ⊤ (f a)).symm.trans
      (congrArg (fun ξ : SchemeFrobeniusMap U.toScheme p => ξ.onOpen ⊤ (f a)) hτ)
  exact (h₁.trans (h₂.trans (h₃.trans h₄))).symm ▸ hI _ hf


open private indices line chart chartOpen relativeBase sourceLine relativeTrace infinityCoefficient
    from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private relativeTrace_operator from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison
open private trace_preserves_map from
  OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialIdeals
open private polynomialCoframe commonChartData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCartierCharts

private def affineCoefficient {R : Type u} [CommRing R] {p : ℕ}
    (φ : SchemeFrobeniusMap (Spec (.of R)) p) : FrobeniusLinearMap R p :=
  (φ.onOpen ⊤).transport
    (StructureSheaf.globalSectionsIso R).symm.commRingCatIsoToRingEquiv

private theorem affineCoefficient_ideal {R : Type u} [CommRing R] {p : ℕ}
    (φ : SchemeFrobeniusMap (Spec (.of R)) p) (I : Ideal R)
    (hI : ∀ a ∈ I.comap (StructureSheaf.globalSectionsIso R).inv.hom,
      φ.onOpen ⊤ a ∈ I.comap (StructureSheaf.globalSectionsIso R).inv.hom) :
    ∀ a ∈ I, affineCoefficient φ a ∈ I := by
  intro a ha
  apply hI ((StructureSheaf.globalSectionsIso R).hom a)
  change (StructureSheaf.globalSectionsIso R).inv
    ((StructureSheaf.globalSectionsIso R).hom a) ∈ I
  exact ((StructureSheaf.globalSectionsIso R).commRingCatIsoToRingEquiv.symm_apply_apply a).symm ▸
      ha

private theorem spec_preserves_top {R : Type u} [CommRing R] {p : ℕ}
    (φ : FrobeniusLinearMap R p) (hp : 0 < p) (I : Ideal R)
    (hI : ∀ a ∈ I, φ a ∈ I) :
    ∀ a ∈ I.comap (StructureSheaf.globalSectionsIso R).inv.hom,
      (φ.toSpec hp).onOpen ⊤ a ∈
        I.comap (StructureSheaf.globalSectionsIso R).inv.hom := by
  let e := (StructureSheaf.globalSectionsIso R).commRingCatIsoToRingEquiv
  apply ring_comap_preserves ((φ.toSpec hp).onOpen ⊤) φ e.symm.toRingHom _ I hI
  intro a
  have h := congrArg (fun ξ : FrobeniusLinearMap R p => ξ (e.symm a))
    (spec_top_transport φ hp)
  change e.symm ((φ.toSpec hp).onOpen ⊤ (e (e.symm a))) = φ (e.symm a) at h
  exact (congrArg (fun b : Γ(Spec (.of R), ⊤) =>
    e.symm ((φ.toSpec hp).onOpen ⊤ b)) (e.apply_symm_apply a)).symm.trans h

private theorem over_component_eq {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens) (f g : M.over U ⟶ N.over U) (h : f = g)
    (V : Over U) (m : M.val.obj (op V.left)) :
    (f.val.app (op V)).hom m = (g.val.app (op V)).hom m :=
  congrArg (fun k : M.over U ⟶ N.over U => (k.val.app (op V)).hom m) h

private theorem affineCoefficient_eq {R : Type u} [CommRing R] {p : ℕ}
    (φ ψ : SchemeFrobeniusMap (Spec (.of R)) p) (h : φ = ψ)
    (I : Ideal R) (hI : ∀ a ∈ I, affineCoefficient ψ a ∈ I) :
    ∀ a ∈ I, affineCoefficient φ a ∈ I := by
  cases h
  exact hI

/-- The coefficient operator of a raw Cartier map in a specified affine coframe. -/
def wordChartCoefficient {C R : Type u} [CommRing C] [CommRing R]
    {p : ℕ} [ExpChar C p] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (k : Spec (.of R) ⟶ X) [IsOpenImmersion k]
    (E : (Scheme.Modules.pullback k).obj L ≅ unitModule (Spec (.of R)))
    (H : (frobeniusRestriction C p base L).over k.opensRange ⟶
      (unitModule X).over k.opensRange) : FrobeniusLinearMap R p :=
  affineCoefficient
    ((framedOpenOperator base L k.opensRange (coframeOverRange k L E) H).openPullback
      k.isoOpensRange.hom)

private theorem wordChartCoefficient_eq {C R : Type u} [CommRing C] [CommRing R]
    {p : ℕ} [ExpChar C p] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (k : Spec (.of R) ⟶ X) [IsOpenImmersion k]
    (E : (Scheme.Modules.pullback k).obj L ≅ unitModule (Spec (.of R)))
    (H H' : (frobeniusRestriction C p base L).over k.opensRange ⟶
      (unitModule X).over k.opensRange) (h : H = H')
    (I : Ideal R) (hI : ∀ a ∈ I, wordChartCoefficient base L k E H' a ∈ I) :
    ∀ a ∈ I, wordChartCoefficient base L k E H a ∈ I := by
  cases h
  exact hI

private theorem relativeFramed_ideal {K A : Type u} [Field K]
    {p : ℕ} [ExpChar K p] [PerfectRing K p] [CommRing A] [Algebra K A]
    (ψ : FrobeniusLinearMap A p) (I : Ideal A) (hI : ∀ a ∈ I, ψ a ∈ I)
    (j : indices.{u})
    (E : (sourceLine (A := A) (p := p)).over (chartOpen A j) ≅
      (unitModule (line A)).over (chartOpen A j)) :
    ∀ a ∈ (I.map Polynomial.C).comap
        (StructureSheaf.globalSectionsIso (Polynomial A)).inv.hom,
      ((framedOpenOperator (relativeBase (K := K) (A := A))
          (sourceLine (A := A) (p := p)) (chartOpen A j) E
          ((relativeTwistedCartierMap (K := K) ψ).over (chartOpen A j))).openPullback
            (chart A j).isoOpensRange.hom).onOpen ⊤ a ∈
        (I.map Polynomial.C).comap
          (StructureSheaf.globalSectionsIso (Polynomial A)).inv.hom := by
  let e := (chart A j).isoOpensRange
  let τ := (polynomialTraceOfOperator (K := K) ψ).toSpec (expChar_pos K p)
  let J := (I.map Polynomial.C).comap
    (StructureSheaf.globalSectionsIso (Polynomial A)).inv.hom
  have htrace : ∀ a ∈ I.map Polynomial.C,
      polynomialTraceOfOperator (K := K) ψ a ∈ I.map Polynomial.C := by
    intro a ha
    simpa only [FrobeniusLinearMap.weight_apply, one_mul] using
      trace_preserves_map (K := K) ψ I hI 1 a ha
  have hτ : ∀ a ∈ J, τ.onOpen ⊤ a ∈ J :=
    spec_preserves_top (polynomialTraceOfOperator (K := K) ψ)
      (expChar_pos K p) (I.map Polynomial.C) htrace
  apply pullback_top_preserves e _ J
  exact framed_top_preserves (relativeBase (K := K) (A := A))
    (sourceLine (A := A) (p := p)) (chartOpen A j) E
    ((relativeTwistedCartierMap (K := K) ψ).over (chartOpen A j))
    (infinityCoefficient (A := A) (p := p) j) (relativeTrace (K := K) ψ j)
    (τ.pushforward e.hom) (relativeTrace_operator (K := K) ψ j)
    (fun V m =>
      (over_component_eq _ _ _ _ _
        (relativeTwistedCartierMap_chart (K := K) ψ j) V m).trans
          (relativeTwistedCartierChart_apply (K := K) ψ j V m))
    (J.comap e.hom.appTop.hom) (pushforward_top_preserves e τ J hτ)

/-- The raw relative Cartier map preserves every polynomial ideal extended
from an ideal preserved by its preceding coefficient operator. -/
theorem relativeWordChart_ideal {K A : Type u} [Field K]
    {p : ℕ} [ExpChar K p] [PerfectRing K p] [CommRing A] [Algebra K A]
    (ψ : FrobeniusLinearMap A p) (I : Ideal A) (hI : ∀ a ∈ I, ψ a ∈ I)
    (j : indices.{u}) {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (L : X.Modules)
    (k : Spec (.of (Polynomial A)) ⟶ X) [IsOpenImmersion k]
    (E : (Scheme.Modules.pullback k).obj L ≅ unitModule (Spec (.of (Polynomial A)))) :
    ∀ a ∈ I.map Polynomial.C,
      wordChartCoefficient base L k E (relativeCartierWordChart ψ j base L k E) a ∈
        I.map Polynomial.C := by
  have h := relativeCartierWordChart_coordinate ψ j base L k E
  apply affineCoefficient_eq _ _ h (I.map Polynomial.C)
  exact affineCoefficient_ideal _ (I.map Polynomial.C)
    (relativeFramed_ideal ψ I hI j
      (coframeOverRange (chart A j) (sourceLine (A := A) (p := p))
        (polynomialCoframe A p j)))

end SchubertGeometry.ProjectiveCartier

namespace SchubertGeometry.RetainedCharacter

open FrobeniusSplitting.RetainedCharacter

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private line chart from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private nodePrior from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordNodeSplittings
open private polynomialLeg nodePolynomial chartRaw from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedWordCartier
open private affinePolynomialMap projectiveRefinement from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps
open private sectionValue from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private retainedChartRange retainedCoordinateIso from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

variable {K R J : Type u} [Field K] [CommRing R] [Algebra K R]
    {p : ℕ} [ExpChar K p] [PerfectRing K p]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (P : ∀ j, Polynomial (N.obj (singletonIndex j)))
    (hP : ∀ j, (P j).natDegree ≤ 2)
    (hr : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom ((P j).coeff 2) =
        (N.map (singletonArrow s k hk)).hom ((P k).coeff 2) * (delta s j hj k hk : N.obj s))
    (base : cN.pt.left ⟶ Spec (.of K))
    (Θ : frobeniusRestriction K p base (matchingModule N cN delta ((p - 1) / 2)) ⟶
      unitModule cN.pt.left)
    (hnorm : Θ.app ⊤
      ((Scheme.Modules.Hom.app
        (coefficientMatchingSection N cN delta (fun j => (P j).coeff 2) hr ((p - 1) / 2)) ⊤).hom
          (1 : Γ(cN.pt.left, ⊤))) = (1 : Γ(cN.pt.left, ⊤)))
    (sel : ∀ s : {s : Finset J // s.Nonempty}, {j // j ∈ s.val})
    {X : Scheme.{u}} (Knode : ∀ s, line (N.obj s) ⟶ X)
    [∀ s, IsOpenImmersion (Knode s)]
    (baseX : X ⟶ Spec (.of K)) (L : X.Modules) (m : unitModule X ⟶ L)
    (E : ∀ s j, (Scheme.Modules.pullback (polynomialLeg N Knode s j)).obj L ≅
      unitModule (Spec (.of (Polynomial (N.obj s)))))

private theorem chartRaw_ideal (s : {s : Finset J // s.Nonempty})
    (j : ULift.{u} (Fin 2)) (I : Ideal (N.obj s))
    (hI : ∀ a ∈ I, nodePrior N cN hcN delta hco hn base Θ s (sel s).1 (sel s).2 a ∈ I) :
    let : IsOpenImmersion (polynomialLeg N Knode s j) := by
      dsimp only [polynomialLeg]
      infer_instance
    ∀ a ∈ I.map Polynomial.C,
      ProjectiveCartier.wordChartCoefficient baseX L (polynomialLeg N Knode s j) (E s j)
        (chartRaw N cN hcN delta hco hn base Θ sel Knode baseX L E s j) a ∈
          I.map Polynomial.C := by
  let : IsOpenImmersion (polynomialLeg N Knode s j) := by
    dsimp only [polynomialLeg]
    infer_instance
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  exact ProjectiveCartier.relativeWordChart_ideal
    (nodePrior N cN hcN delta hco hn base Θ s (sel s).1 (sel s).2)
    I hI j baseX L (polynomialLeg N Knode s j) (E s j)

end SchubertGeometry.RetainedCharacter
