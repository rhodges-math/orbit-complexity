import OrbitComplexity.Paper.Deodhar.RootMaps
import OrbitComplexity.SchubertGeometry.FlagVariety.Points
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Group
import OrbitComplexity.SchubertGeometry.Deodhar.Products

/-! # Ordered root products of subexpressions

The omitted and decreasing positions retain their original order. Their conjugated root
parameters factor every Deodhar prefix, and torus conjugation rescales each parameter by its
negative signed-root character. The signed prefix representative absorbs the remaining torus
factor after projection to flags.

## Main definitions and results

* `SchubertGeometry.subwordRootProduct`: the selected root product in a prefix.
* `SchubertGeometry.deodharPrefix_rootProduct`: its factorization of the Deodhar prefix.
* `subwordRootProduct_torus_points`: character scaling of the root product.
* `subwordRootProduct_flag_action`: character scaling of the represented flag.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Section 5.
-/

noncomputable section
namespace SchubertOrbits

export SchubertGeometry (subwordRootProduct deodharPrefix_rootProduct)
open BruhatIntervals ReductiveGroups TauCeti GroupActions AlgebraicGeometry SchubertGeometry
open SchubertOrbits
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private def selectedPosition (j : Fin word.length) : Option
    {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} := by
  classical
  exact if h : j ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression then
    some ⟨j, h⟩ else none

private theorem rootProduct_expansion
    (parameters : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} → K)
    (n : ℕ) :
    SchubertGeometry.subwordRootProduct G expression parameters n =
      ((((List.finRange word.length).take n).filterMap (selectedPosition G expression)).map
        (fun j => gaParameterPoint (SchubertGeometry.subwordRootMap G expression j)
          (parameters j))).prod := rfl

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] torusReduced

/-- Conjugating the ordered root product rescales each parameter by its root character. -/
theorem subwordRootProduct_torus_points
    (parameters : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} → K)
    (n : ℕ) (t : (torusVariety G).points) :
    (torusPointsMulEquiv G t : G.points) * SchubertGeometry.subwordRootProduct G expression
      parameters n *
        (torusPointsMulEquiv G t : G.points)⁻¹ =
      SchubertGeometry.subwordRootProduct G expression (fun j => affinePointsEquiv.symm t
        ((torusCoordinateEquiv G).symm (MonoidAlgebra.single (subwordCharacter G expression j) 1)) *
          parameters j) n := by
  have h := map_list_prod (MulAut.conj (torusPointsMulEquiv G t : G.points)).toMonoidHom
    ((((List.finRange word.length).take n).filterMap (selectedPosition G expression)).map
      (fun j => gaParameterPoint (SchubertGeometry.subwordRootMap G expression j) (parameters j)))
  simp only [List.map_map, Function.comp_def, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, subwordRootMap_torus_points] at h
  simpa only [rootProduct_expansion] using h

/-- Torus action on the represented flag rescales the selected root coordinates. -/
theorem subwordRootProduct_flag_action
    (parameters : {position : Fin word.length //
      position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} → K)
    (n : ℕ) (t : (torusVariety G).points) :
    (torusPointsMulEquiv G t : G.points) • flagProjection G
        (SchubertGeometry.subwordRootProduct G expression parameters n *
          SchubertGeometry.subwordRepresentative G expression n) =
      flagProjection G (SchubertGeometry.subwordRootProduct G expression (fun j =>
        affinePointsEquiv.symm t
        ((torusCoordinateEquiv G).symm (MonoidAlgebra.single (subwordCharacter G expression j) 1)) *
          parameters j) n * SchubertGeometry.subwordRepresentative G expression n) := by
  change flagProjection G ((torusPointsMulEquiv G t : G.points) * _) = _
  apply (flagProjection_eq_iff G _ _).mpr
  have hT : (SchubertGeometry.subwordRepresentative G expression n)⁻¹ *
        (torusPointsMulEquiv G t : G.points)⁻¹ * SchubertGeometry.subwordRepresentative G
          expression n ∈
      G.torusPoints :=
    (Subgroup.mem_normalizer_iff''.mp (SchubertGeometry.subwordRepresentative_mem_normalizer G
      expression n)
      (torusPointsMulEquiv G t : G.points)⁻¹).mp
        (G.torusPoints.inv_mem (torusPointsMulEquiv G t).property)
  rw [← subwordRootProduct_torus_points G expression parameters n t]
  convert G.torus_le_borel hT using 1
  group

end SchubertOrbits
