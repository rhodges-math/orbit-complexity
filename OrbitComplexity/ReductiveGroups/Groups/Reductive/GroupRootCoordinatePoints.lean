import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCoordinates

/-!
# Rational evaluation of root coordinates

The polynomial root chart evaluates to the ordered product of the chosen root
parameters, with the coordinate roots reindexed by the positive root support.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Evaluating root-subgroup coordinates gives the ordered root-map product. -/
theorem rootSubsetCoordinateEquiv_eval (R : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R)
    (a : {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} → K) :
    ((MvPolynomial.aeval a).comp (G.rootSubsetCoordinateEquiv R hR).toAlgHom).comp
        (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal R hR).toIdeal) =
      ((G.rootSubsetOrder R).map (fun i =>
        gaParameterPoint (G.borelRootMaps i.val)
          (a (G.rootSubsetIndexEquiv R i)))).prod.ofConv := by
  have h := gaProductCoordinate_eval
    (fun i : G.rootCharacters R => G.borelRootMaps i.val) (G.rootSubsetOrder R)
    (fun i => a (G.rootSubsetIndexEquiv R i))
  apply AlgHom.ext
  intro b
  change MvPolynomial.aeval a
    (G.rootSubsetCoordinateEquiv R hR (Ideal.Quotient.mk _ b)) = _
  rw [G.rootSubsetCoordinateEquiv_mk, MvPolynomial.aeval_rename]
  exact DFunLike.congr_fun h b

end ReductiveGroups.ReductiveGroupData
