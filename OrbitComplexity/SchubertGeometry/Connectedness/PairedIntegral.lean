import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.EndpointFibres
import OrbitComplexity.SchubertGeometry.Connectedness.RichardsonConnected
import OrbitComplexity.FrobeniusSplitting.Normality.IntegralSource

set_option autoImplicit false

/-! # Integral paired Bott–Samelson sources

The contraction and reflection-curve graph gives connectedness of the
Richardson target. Properness, connected geometric fibres and domain stalks
then give integrality of the paired source. The generic field-base argument
precedes its application to the paired endpoint.
-/

namespace SchubertGeometry

open AlgebraicGeometry CategoryTheory ReductiveGroups

universe u

/-- Over a field, a proper endpoint with connected geometric fibres and
domain source stalks has integral source if its finite-type target is connected. -/
theorem isIntegral_of_connected_endpoint {L : Type u} [Field L]
    {X Y : Scheme.{u}} (base : Y ⟶ Spec (.of L)) [LocallyOfFiniteType base]
    (f : X ⟶ Y) [IsProper f] [GeometricallyConnected f] [ConnectedSpace Y]
    (hd : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsIntegral X := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian base
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact FrobeniusSplitting.isIntegral_of_proper f hd

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

/-- A nonempty Richardson variety is connected by its cell contractions
and reflection-curve graph. -/
theorem richardson_connected_of_le (a b : G.weylGroup)
    (hab : WeylBruhatLE G.rootBase a b) :
    ConnectedSpace (richardsonVariety G a b).scheme :=
  CellContraction.richardson_connected_graph G a b hab

/-- The paired Bott–Samelson source is integral whenever its Richardson target
is nonempty. -/
theorem pairedSource_integral (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (hab : WeylBruhatLE G.rootBase
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)) :
    IsIntegral (pairedBSDHSource G a b).left := by
  let : ConnectedSpace (richardsonVariety G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).scheme :=
    richardson_connected_of_le G _ _ hab
  let : GeometricallyConnected (pairedRichardsonMap G a b ha hb).left :=
    pairedEndpoint_connected G a b ha hb
  exact isIntegral_of_connected_endpoint
    (richardsonVariety G
      (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)).toSpec
    (pairedRichardsonMap G a b ha hb).left
    (fun x => (pairedBSDHSource_stalks G a b x).1)

end SchubertGeometry
