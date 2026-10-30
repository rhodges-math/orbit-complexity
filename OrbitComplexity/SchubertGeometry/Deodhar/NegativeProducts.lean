import OrbitComplexity.SchubertGeometry.Deodhar.Products
import OrbitComplexity.SchubertGeometry.Deodhar.Representatives
import OrbitComplexity.SchubertGeometry.Deodhar.StepRoots
import OrbitComplexity.SchubertGeometry.Deodhar.OppositeRootPoints

/-! # Opposite-unipotent products of distinguished subexpressions

The signed simple-root factors have negative transported roots. Their conjugates and ordered
products therefore lie in the opposite unipotent subgroup.
-/

open BruhatIntervals ReductiveGroups TauCeti
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

attribute [local irreducible] subwordRepresentative gaParameterPoint deodharRootElement

set_option maxHeartbeats 400000 in
private theorem rootElement_conj_opposite
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (j : Fin word.length)
    (hj : j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
      negativeSteps (weylCoxeterSystem G.rootBase) expression) (t : K) :
    subwordRepresentative G expression j.val * deodharRootElement G expression (fun _ => t) j *
      (subwordRepresentative G expression j.val)⁻¹ ∈ G.oppositeUnipotentPoints := by
  classical
  let r : G.points := subwordRepresentative G expression j.val
  let w : G.weylGroup := expression.prefixProd (weylCoxeterSystem G.rootBase) j.val
  let i : G.rootBase.support := word.get j
  have htr : G.rootPointTransport r (G.rootSystem.weylGroupToPerm w) :=
    subwordRepresentative_transport G expression j.val
  change r * deodharRootElement G expression (fun _ => t) j * r⁻¹ ∈ _
  by_cases hn : j ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression
  · have hi : ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val) :=
      negativeStep_root G.rootBase expression j hn
    simp only [deodharRootElement, hn, ↓reduceIte]
    exact positiveSimple_conj_opposite G r w htr i hi t
  · have he := hj.resolve_right hn
    have hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val) :=
      equalStep_root G.rootBase expression hd j he
    simp only [deodharRootElement, hn, he, ↓reduceIte]
    exact negativeSimple_conj_opposite G r w htr i hi t

/-- A selected root parameter of a distinguished subexpression lies in the opposite unipotent. -/
theorem subwordRootMap_mem_opposite
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (j : {position : Fin word.length //
      position ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (weylCoxeterSystem G.rootBase) expression}) (t : K) :
    gaParameterPoint (subwordRootMap G expression j) t ∈ G.oppositeUnipotentPoints := by
  have hp := subwordRootMap_point G expression (fun _ => t) j
  exact (congrArg (fun a : G.points => a ∈ G.oppositeUnipotentPoints) hp).mpr
    (rootElement_conj_opposite G expression hd j.val j.property t)

/-- An ordered prefix of distinguished root parameters lies in the opposite unipotent. -/
theorem subwordRootProduct_mem_opposite
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (parameters : {position : Fin word.length //
      position ∈ equalSteps (weylCoxeterSystem G.rootBase) expression ∪
        negativeSteps (weylCoxeterSystem G.rootBase) expression} → K) (n : ℕ) :
    subwordRootProduct G expression parameters n ∈ G.oppositeUnipotentPoints := by
  unfold subwordRootProduct
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
  exact subwordRootMap_mem_opposite G expression hd j (parameters j)

/-- A distinguished prefix is an opposite-unipotent point times its signed representative. -/
theorem deodharPrefix_mem_opposite
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (parameters : Fin word.length → K) (n : ℕ) :
    ∃ u ∈ G.oppositeUnipotentPoints, deodharPrefix G expression parameters n =
      u * subwordRepresentative G expression n := by
  exact ⟨subwordRootProduct G expression (fun j => parameters j.val) n,
    subwordRootProduct_mem_opposite G expression hd _ n,
    deodharPrefix_rootProduct G expression parameters n⟩

end
end SchubertGeometry
