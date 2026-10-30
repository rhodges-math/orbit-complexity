import OrbitComplexity.GroupActions.Tori.RootConjugation
import OrbitComplexity.GroupActions.Actions.EquivariantPoints
import OrbitComplexity.GroupActions.Tori.WeightedAction
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCoordinatePoints
import OrbitComplexity.GroupActions.Varieties.AffineMorphisms

/-! # Root charts and diagonal torus weights

The ordered root-subgroup chart intertwines torus conjugation with the diagonal affine
action of the root characters. Its equivariance follows from the root parameters
and their torus conjugation formulas.

## Main results

* `GroupActions.rootSubsetChart_isModHom`: equivariance of the ordered root chart.
 -/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
noncomputable section
universe u
namespace GroupActions
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)
  (R : Set G.rootIndex) (hR : ReductiveGroups.IsPositiveRootClosed G.rootBase R)

omit [IsAlgClosed K] [CharZero K] in
private theorem weightCharacter_eq_of_mapDomain (t : (torusVariety G).points)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K))
    (hz : (torusPointsMulEquiv G t : G.points) = TauCeti.AlgHom.mapDomain G.torusSplit z)
    (w : G.torusIndex →₀ ℤ) :
    torusWeightCharacter G w t = z.ofConv (MonoidAlgebra.single (Multiplicative.ofAdd w) 1) := by
  obtain ⟨a, ha⟩ := G.split_surjective (MonoidAlgebra.single (Multiplicative.ofAdd w) 1)
  have e := congrArg (fun v : G.points => v.ofConv a) hz
  rw [torusPointsMulEquiv_coe] at e
  change affinePointsEquiv.symm t (Ideal.Quotient.mk G.torusIdeal.toIdeal a) =
    z.ofConv (G.torusSplit a) at e
  change affinePointsEquiv.symm t ((torusCoordinateEquiv G).symm
    (MonoidAlgebra.single (Multiplicative.ofAdd w) 1)) = _
  have hc : (torusCoordinateEquiv G).symm
      (MonoidAlgebra.single (Multiplicative.ofAdd w) 1) =
        Ideal.Quotient.mk G.torusIdeal.toIdeal a :=
    (congrArg (torusCoordinateEquiv G).symm ((torusCoordinateEquiv_mk G a).trans ha)).symm.trans
      ((torusCoordinateEquiv G).symm_apply_apply _)
  exact (congrArg (affinePointsEquiv.symm t) hc).trans (e.trans (congrArg z.ofConv ha))

private theorem rootIndex_character (i : G.rootCharacters R) :
    G.rootCharacter (G.rootSubsetIndexEquiv R i).val = i.val.val := by
  change (G.characterRootEquiv.symm (G.characterRootEquiv _)).val = i.val.val
  rw [Equiv.symm_apply_apply]
  rfl

private theorem rootChart_points
    (a : {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} → K) :
    (rootSubsetPointsMulEquiv G R hR
      (Variety.mapPoints (rootSubsetChart G R hR).hom
        ((affineSpaceVarietyPointsEquiv K _).symm a)) : G.points) =
      ((G.rootSubsetOrder R).map (fun i =>
        ReductiveGroups.gaParameterPoint (G.borelRootMaps i.val)
          (a (G.rootSubsetIndexEquiv R i)))).prod := by
  let e : (affineVariety K (G.rootSubsetAlgebra R hR)).points ≃*
      G.rootSubsetPoints R hR := rootSubsetPointsMulEquiv G R hR
  change (e
    (Variety.mapPoints (affineMorphism (G.rootSubsetCoordinateEquiv R hR).toAlgHom)
      ((affineVarietyPointsEquiv K _).symm (MvPolynomial.aeval a))) : G.points) = _
  rw [affineMorphism_points]
  have h := G.rootSubsetCoordinateEquiv_eval R hR a
  apply WithConv.ofConv_injective
  change ((affinePointsEquiv.symm (affinePointsEquiv
    ((MvPolynomial.aeval a).comp (G.rootSubsetCoordinateEquiv R hR).toAlgHom))).comp
      (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal R hR).toIdeal)) = _
  rw [Equiv.symm_apply_apply]
  exact h

private theorem rootProduct_conjugate
    (a : {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} → K)
    (z : WithConv (MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) →ₐ[K] K)) :
    ((G.rootSubsetOrder R).map (fun i =>
      ReductiveGroups.gaParameterPoint (G.borelRootMaps i.val)
        (a (G.rootSubsetIndexEquiv R i) * z.ofConv (MonoidAlgebra.single
          (G.rootCharacter (G.rootSubsetIndexEquiv R i).val) 1)))).prod =
      TauCeti.AlgHom.mapDomain G.torusSplit z *
        ((G.rootSubsetOrder R).map (fun i =>
          ReductiveGroups.gaParameterPoint (G.borelRootMaps i.val)
            (a (G.rootSubsetIndexEquiv R i)))).prod *
        (TauCeti.AlgHom.mapDomain G.torusSplit z)⁻¹ := by
  have hxU (i) : ReductiveGroups.gaAffineGroupTangent (G.borelRootMaps i) ∈
      G.unipotentTangent := G.borelRootBasis_tangent i ▸ (G.borelRootBasis i).property
  have hc := ReductiveGroups.borelRootSubsetProduct_torus_conj G.borelIdeal G.torusSplit
    G.split_surjective G.borelRootMaps hxU G.borelRootMaps_weight (G.rootCharacters R)
    (G.rootSubsetOrder R) (fun i => a (G.rootSubsetIndexEquiv R i)) z
  let a' := fun r : {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} =>
    a r * z.ofConv (MonoidAlgebra.single (G.rootCharacter r.val) 1)
  have hb : (fun i : G.rootCharacters R => a' (G.rootSubsetIndexEquiv R i)) =
      (fun i => z.ofConv (MonoidAlgebra.single i.val.val 1) *
        a (G.rootSubsetIndexEquiv R i)) := by
    funext i
    dsimp only [a']
    rw [rootIndex_character G R i]
    exact mul_comm _ _
  have hh := congrArg (fun b : G.rootCharacters R → K =>
    ((G.rootSubsetOrder R).map (fun i =>
      ReductiveGroups.gaParameterPoint (G.borelRootMaps i.val) (b i))).prod) hb
  exact hh.trans hc.symm

/-- The ordered root chart is equivariant for the diagonal character action. -/
theorem rootSubsetChart_isModHom :
    letI := weightedAffineAction G
      (fun r : {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} =>
        Multiplicative.toAdd (G.rootCharacter r.val))
    letI := rootConjugationAction G R hR
    IsModHom (torusVariety G).toOver (rootSubsetChart G R hR).hom := by
  let w := fun r : {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} =>
    Multiplicative.toAdd (G.rootCharacter r.val)
  let := weightedAffineAction G w
  let := rootConjugationAction G R hR
  apply Variety.isModHom_of_points (torusVariety G)
    (affineSpaceVariety K {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R})
    (rootSubsetVariety G R hR)
  intro t x
  obtain ⟨a, rfl⟩ := (affineSpaceVarietyPointsEquiv K
    {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R}).symm.surjective x
  obtain ⟨z, hz⟩ := (ReductiveGroups.mem_torusPoints_iff G.torusIdeal G.torusSplit
    G.split_surjective G.split_eq_zero (torusPointsMulEquiv G t)).mp
      (torusPointsMulEquiv G t).property
  let a' := fun r : {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} =>
    a r * z.ofConv (MonoidAlgebra.single (G.rootCharacter r.val) 1)
  have hcoordinates :
      t • (affineSpaceVarietyPointsEquiv K _).symm a =
        (affineSpaceVarietyPointsEquiv K _).symm a' := by
    apply (affineSpaceVarietyPointsEquiv K _).injective
    funext i
    rw [weightedAffineAction_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change a i * torusWeightCharacter G (w i) t = a' i
    rw [weightCharacter_eq_of_mapDomain G t z hz]
    rfl
  apply (rootSubsetPointsMulEquiv G R hR).injective
  apply Subtype.ext
  rw [hcoordinates, rootChart_points, rootConjugationAction_smul, rootChart_points, hz]
  exact rootProduct_conjugate G R a z

end GroupActions
