import OrbitComplexity.SchubertGeometry.BSDH.Construction
import OrbitComplexity.GroupActions.Varieties.Normal
import OrbitComplexity.FrobeniusSplitting.Normality.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral

/-! # Varieties underlying iterated simple-Schubert schemes

Smoothness gives regular local rings on every geometric fibre. Together with geometric
connectedness this gives geometric integrality. The proper smooth structure morphism then
defines a variety, and its stalks are integrally closed domains.
-/

open CategoryTheory AlgebraicGeometry

namespace SchubertGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- Every iterated simple-Schubert scheme has integral geometric fibres over the field. -/
instance bsdh_geomIntegral (word : List G.rootBase.support) :
    GeometricallyIntegral (bsdhToSpec G word) :=
  TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral (bsdhToSpec G word)

/-- The iterated simple-Schubert scheme is integral. -/
instance bsdh_integral (word : List G.rootBase.support) : IsIntegral (bsdhScheme G word) :=
  GeometricallyIntegral.isIntegral_of_subsingleton (bsdhToSpec G word)

/-- The variety on the proper smooth iterated simple-Schubert scheme. -/
abbrev bsdhVariety (word : List G.rootBase.support) : GroupActions.Variety K where
  scheme := bsdhScheme G word
  toSpec := bsdhToSpec G word

/-- Every local ring of the iterated simple-Schubert variety is an integrally closed domain. -/
theorem bsdhVariety_isNormal (word : List G.rootBase.support) :
    (bsdhVariety G word).IsNormal := by
  exact @FrobeniusSplitting.stalks_of_smooth K _ (bsdhScheme G word)
    (bsdhToSpec G word) (bsdh_smooth G word)

end

end SchubertGeometry
