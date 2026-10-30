import OrbitComplexity.SchubertGeometry.BSDH.RichardsonMap
import OrbitComplexity.SchubertGeometry.Cells.RichardsonIntegral

/-! # Integral normal sources of Richardson endpoints

Bruhat comparability makes the reduced Richardson target integral. Proper
connected-fibre descent gives connectedness of the paired source, whose domain
stalks then imply integrality. Reduced words supply a source for every target.
-/

open CategoryTheory AlgebraicGeometry SchubertGeometry ReductiveGroups
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem pairedSource_integral (a b : List G.rootBase.support)
    (ha : (weylCoxeterSystem G.rootBase).IsReduced a)
    (hb : (weylCoxeterSystem G.rootBase).IsReduced b)
    (hle : WeylBruhatLE G.rootBase (G.longestElement * simpleWeylWord G.rootBase b)
      (simpleWeylWord G.rootBase a)) : IsIntegral (pairedBSDHSource G a b).left := by
  let lower := G.longestElement * simpleWeylWord G.rootBase b
  let upper := simpleWeylWord G.rootBase a
  let f := pairedRichardsonMap G a b ha hb
  have : IsIntegral (richardsonVariety G lower upper).scheme :=
    richardsonVariety_integral G lower upper hle
  have : ConnectedSpace (richardsonVariety G lower upper).toOver.left := by
    change ConnectedSpace (richardsonVariety G lower upper).scheme
    infer_instance
  have : IsLocallyNoetherian (richardsonVariety G lower upper).toOver.left := by
    change IsLocallyNoetherian (richardsonVariety G lower upper).scheme
    exact LocallyOfFiniteType.isLocallyNoetherian (richardsonVariety G lower upper).toSpec
  have : IsLocallyNoetherian (pairedBSDHSource G a b).left :=
    LocallyOfFiniteType.isLocallyNoetherian f.left
  have : GeometricallyConnected f.left := pairedRichardsonMap_geomConnected G a b ha hb
  exact FrobeniusSplitting.isIntegral_of_proper f.left
    (fun z => (pairedBSDHSource_stalks G a b z).1)

end
end SchubertGeometry
