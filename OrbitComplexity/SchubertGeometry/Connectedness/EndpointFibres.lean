import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.BSDH.ConnectedFibres
import OrbitComplexity.SchubertGeometry.BSDH.RichardsonMap

set_option autoImplicit false

/-! # Connected geometric fibres of Bott–Samelson endpoints

The reduced-word Schubert endpoint and the paired Richardson endpoint have
geometrically connected fibres. Cartesian transport is proved for arbitrary
schemes before it is applied to the Schubert and Richardson endpoints.
-/

namespace SchubertGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReductiveGroups

universe u

/-- Geometric connectedness passes through the specified Cartesian square. -/
theorem geomConnected_of_square {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (qX : X' ⟶ X) (qY : Y' ⟶ Y)
    (h : IsPullback qX f' f qY) [GeometricallyConnected f] :
    GeometricallyConnected f' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @GeometricallyConnected) h inferInstance

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

/-- The reduced-word Schubert endpoint has connected geometric fibres. -/
theorem schubertEndpoint_connected (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word) :
    GeometricallyConnected (bsdhSchubertMap G word hred).left :=
  bsdhSchubert_geomConnected G word hred

/-- A Cartesian base change of the reduced-word Schubert endpoint has
connected geometric fibres. -/
theorem schubertEndpoint_baseChange (word : List G.rootBase.support)
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (qX : X ⟶ (bsdhVariety G word).scheme)
    (qY : Y ⟶ (schubertVariety G (simpleWeylWord G.rootBase word)).scheme)
    (h : IsPullback qX f (bsdhSchubertMap G word hred).left qY) :
    GeometricallyConnected f := by
  let : GeometricallyConnected (bsdhSchubertMap G word hred).left :=
    schubertEndpoint_connected G word hred
  exact geomConnected_of_square (bsdhSchubertMap G word hred).left f qX qY h

/-- The paired Richardson endpoint has connected geometric fibres. -/
theorem pairedEndpoint_connected (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b) :
    GeometricallyConnected (pairedRichardsonMap G a b ha hb).left :=
  pairedRichardsonMap_geomConnected G a b ha hb

/-- A Cartesian base change of the paired Richardson endpoint has connected
geometric fibres. -/
theorem pairedEndpoint_baseChange (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (qX : X ⟶ (pairedBSDHSource G a b).left)
    (qY : Y ⟶ (richardsonVariety G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).scheme)
    (h : IsPullback qX f (pairedRichardsonMap G a b ha hb).left qY) :
    GeometricallyConnected f := by
  let : GeometricallyConnected (pairedRichardsonMap G a b ha hb).left :=
    pairedEndpoint_connected G a b ha hb
  exact geomConnected_of_square (pairedRichardsonMap G a b ha hb).left f qX qY h

end SchubertGeometry
