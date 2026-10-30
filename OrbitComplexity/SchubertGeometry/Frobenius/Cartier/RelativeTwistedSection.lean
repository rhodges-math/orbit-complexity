import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedGlobal
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedSectionComparison
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalGenerators
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Inserting a section into the relative Cartier map

The morphism on the original source line is compared on its polynomial charts.
The passage from a morphism out of a Frobenius-restricted unit to an operator
is made over an arbitrary scheme.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting FrobeniusSplitting.OperatorSheaf

noncomputable section
universe u v

namespace SchubertGeometry.ProjectiveCartier

open RelativeGlue

open private indices line chart chartOpen relativeBase sourceLine unitLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

open private twistModuleMap
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedWeights

open private insertedInfinity auxiliaryOperator
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections

open private chart_precompose_global
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison

open private polynomial_charts_iSup
  from OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalGenerators

private theorem iso_map_eq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {M N : C} (f g : M ⟶ N)
    (h : F.map f = F.map g) : G.map f = G.map g := by
  apply (cancel_epi (e.hom.app M)).mp
  calc
    e.hom.app M ≫ G.map f = F.map f ≫ e.hom.app N :=
      (e.hom.naturality f).symm
    _ = F.map g ≫ e.hom.app N := congrArg (fun k => k ≫ e.hom.app N) h
    _ = e.hom.app M ≫ G.map g := e.hom.naturality g

private theorem restrict_eq_of_over {X : Scheme.{u}} (U : X.Opens)
    {M N : X.Modules} (f g : M ⟶ N) (h : f.over U = g.over U) :
    (Scheme.Modules.restrictFunctor U.ι).map f =
      (Scheme.Modules.restrictFunctor U.ι).map g := by
  apply iso_map_eq (Scheme.Modules.overFunctorEquiv U) f g
  exact congrArg
    (fun k : M.over U ⟶ N.over U => (Scheme.Modules.overEquiv U).functor.map k) h

private theorem hom_eq_of_over_cover {X : Scheme.{u}} {I : Type v}
    (U : I → X.Opens) (hc : iSup U = ⊤) {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ i, f.over (U i) = g.over (U i)) : f = g := by
  have hrange : (⨆ i, (U i).ι.opensRange) = ⊤ := by
    simpa only [Scheme.Opens.opensRange_ι] using hc
  exact ProjectiveLine.module_hom_ext_cover (fun i => (U i).ι) hrange f g
    (fun i => restrict_eq_of_over (U i) f g (h i))

private theorem over_comp {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (U : X.Opens) :
    (f ≫ g).over U = f.over U ≫ g.over U := rfl

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

private theorem relative_precompose (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) :
    twistModuleMap (C := K) (q := p) (relativeBase (K := K) (A := A)) m ≫
        relativeTwistedCartierMap (K := K) ψ =
      schemeOperatorHom (relativeBase (K := K) (A := A))
        (auxiliaryOperator (K := K) ψ m) := by
  apply hom_eq_of_over_cover (chartOpen A) (polynomial_charts_iSup A)
  intro j
  calc
    _ = (twistModuleMap (C := K) (q := p) (relativeBase (K := K) (A := A)) m).over
          (chartOpen A j) ≫
        (relativeTwistedCartierMap (K := K) ψ).over (chartOpen A j) :=
      over_comp _ _ _
    _ = (twistModuleMap (C := K) (q := p) (relativeBase (K := K) (A := A)) m).over
          (chartOpen A j) ≫ relativeTwistedCartierChart (K := K) ψ j :=
      congrArg
        (fun t : (frobeniusRestriction K p (relativeBase (K := K) (A := A))
            (sourceLine (A := A) (p := p))).over (chartOpen A j) ⟶
              (unitLine (A := A)).over (chartOpen A j) =>
          (twistModuleMap (C := K) (q := p) (relativeBase (K := K) (A := A)) m).over
            (chartOpen A j) ≫ t)
        (relativeTwistedCartierMap_chart (K := K) ψ j)
    _ = _ := chart_precompose_global (K := K) ψ m j

/-- Inserting a global section into the glued relative Cartier morphism gives
the relative operator with that same section and its original infinity factor. -/
theorem twistedSectionOperator_relative (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) :
    twistedSectionOperator (relativeBase (K := K) (A := A))
        (sourceLine (A := A) (p := p)) (relativeTwistedCartierMap (K := K) ψ)
        ((m.val.app (op ⊤)).hom (1 : Γ(line A, ⊤))) =
      relativeCartierOperator (K := K) ψ (insertedInfinity m) := by
  exact twistedSectionOperator_eq (relativeBase (K := K) (A := A))
    (sourceLine (A := A) (p := p)) (relativeTwistedCartierMap (K := K) ψ) m
    (auxiliaryOperator (K := K) ψ m) (relative_precompose (K := K) ψ m)


end SchubertGeometry.ProjectiveCartier
