import OrbitComplexity.SchubertGeometry.Deodhar.Elements
import Mathlib.Data.List.FinRange

/-! # Signed prefix representatives

Signed representatives of subexpressions normalize the torus. Their adjoint action on root
spaces agrees with the Weyl action of the corresponding subexpression prefix.

## Main results

* `subwordRepresentative_transport`: root-space transport by the signed prefix product.
* `subwordRepresentative_mem_normalizer`: membership in the torus normalizer.

## References

* R. J. Marsh and K. Rietsch, *Parametrizations of flag varieties*, Section 5.
-/

noncomputable section
namespace SchubertGeometry
open BruhatIntervals TauCeti ReductiveGroups
private theorem equal_iff_choice {S W : Type*} [Group W] {M : CoxeterMatrix S}
    (cs : CoxeterSystem M W) {word : List S} (expression : Subexpression word)
    (j : Fin word.length) : j ∈ equalSteps cs expression ↔
      expression.choices[j.val]'(by rw [expression.length_choices]; exact j.isLt) = false := by
  have hsimple : cs.simple word[j.val] ≠ 1 := by
    intro h
    have hlen := congrArg cs.length h
    exact Nat.one_ne_zero (by simpa only [cs.length_simple, cs.length_one] using hlen)
  change expression.prefixProd cs j.val = expression.prefixProd cs (j.val + 1) ↔ _
  rw [expression.prefixProd_succ cs j]
  cases hc : expression.choices[j.val]'(by rw [expression.length_choices]; exact j.isLt)
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
  · simp only [↓reduceIte, Bool.true_eq_false, iff_false]
    intro h
    apply hsimple
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem rootTransport_inv {g : G.points} {σ : Equiv.Perm G.rootIndex}
    (h : G.rootPointTransport g σ) : G.rootPointTransport g⁻¹ σ⁻¹ := by
  intro r
  have hcomp :
      ((affineGroupAdjointLieEquiv g⁻¹).toLinearEquiv.toLinearMap).comp
        ((affineGroupAdjointLieEquiv g).toLinearEquiv.toLinearMap) = LinearMap.id := by
    apply LinearMap.ext
    intro d
    change affineGroupAdjointRepresentation g⁻¹ (affineGroupAdjointRepresentation g d) = d
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hinv := congrArg (fun S : Submodule K G.tangent => S.map
    ((affineGroupAdjointLieEquiv g⁻¹).toLinearEquiv.toLinearMap)) (h (σ⁻¹ r))
  simp only [← Submodule.map_comp, hcomp, Submodule.map_id] at hinv
  simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using hinv.symm

private theorem inverseReflection_transport (r : G.rootIndex) :
    G.rootPointTransport (G.reflectionPoint r)⁻¹ (G.rootSystem.reflectionPerm r) := by
  have hr : G.rootPointTransport (G.reflectionPoint r) (G.rootSystem.reflectionPerm r) :=
    G.isBruhatSystem.weyl.transport_reflection r
  have hinv : G.rootPointTransport (G.reflectionPoint r)⁻¹
      (G.rootSystem.reflectionPerm r)⁻¹ := rootTransport_inv G hr
  simpa only [RootPairing.reflectionPerm_inv] using hinv

variable {word : List G.rootBase.support} (expression : Subexpression word)

private def chosenFactor (j : Fin word.length) : G.weylGroup :=
  if expression.choices[j.val]'(by rw [expression.length_choices]; exact j.isLt) then
    (ReductiveGroups.weylCoxeterSystem G.rootBase).simple word[j.val] else 1

set_option maxHeartbeats 400000 in
private theorem step_transport (j : Fin word.length) :
    G.rootPointTransport (subwordStepPoint G expression j)
      (G.rootSystem.weylGroupToPerm (chosenFactor G expression j)) := by
  classical
  have hequal := equal_iff_choice (ReductiveGroups.weylCoxeterSystem G.rootBase) expression j
  by_cases hn : j ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression
  · have hc : expression.choices[j.val]'(by
        rw [expression.length_choices]; exact j.isLt) = true := by
      apply Bool.eq_true_of_not_eq_false
      intro hf
      exact hn.2 ((hequal.mpr hf).symm)
    simp only [subwordStepPoint, simpleRepresentative, inv_inv, hn, ↓reduceIte,
      chosenFactor, hc,
      ReductiveGroups.weylCoxeterSystem_simple, ReductiveGroups.weylGroupToPerm_simple]
    exact G.isBruhatSystem.weyl.transport_reflection _
  · by_cases he : j ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression
    · have hc := hequal.mp he
      simp only [subwordStepPoint, hn, he, ↓reduceIte,
        chosenFactor, hc,
        Bool.false_eq_true, map_one]
      exact G.isBruhatSystem.weyl.transport_one
    · have hc : expression.choices[j.val]'(by
          rw [expression.length_choices]; exact j.isLt) = true := by
        apply Bool.eq_true_of_not_eq_false
        exact fun hf => he (hequal.mpr hf)
      simp only [subwordStepPoint, simpleRepresentative, hn, he, ↓reduceIte,
        chosenFactor, hc,
        ReductiveGroups.weylCoxeterSystem_simple, ReductiveGroups.weylGroupToPerm_simple]
      exact inverseReflection_transport G _

private theorem chosenFactor_list :
    List.ofFn (chosenFactor G expression) =
      expression.factors (ReductiveGroups.weylCoxeterSystem G.rootBase) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, expression.length_factors]
  · intro j hj hk
    simp only [List.getElem_ofFn, Subexpression.factors, List.getElem_map,
      List.getElem_zip, chosenFactor]

private theorem list_transport (l : List (Fin word.length)) :
    G.rootPointTransport ((l.map (subwordStepPoint G expression)).prod)
      (G.rootSystem.weylGroupToPerm ((l.map (chosenFactor G expression)).prod)) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, map_one]
    exact G.isBruhatSystem.weyl.transport_one
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul]
    exact G.isBruhatSystem.weyl.transport_mul _ _ _ _ (step_transport G expression j) ih

/-- A signed prefix product transports root spaces by its subexpression's Weyl prefix. -/
theorem subwordRepresentative_transport (n : ℕ) :
    G.rootPointTransport (subwordRepresentative G expression n)
      (G.rootSystem.weylGroupToPerm
        (expression.prefixProd (ReductiveGroups.weylCoxeterSystem G.rootBase) n)) := by
  have h := list_transport G expression ((List.finRange word.length).take n)
  simp only [List.map_take, ← List.ofFn_eq_map, chosenFactor_list] at h
  exact h

/-- Every signed subexpression prefix belongs to the normalizer of the torus. -/
theorem subwordRepresentative_mem_normalizer (n : ℕ) :
    subwordRepresentative G expression n ∈ Subgroup.normalizer (G.torusPoints : Set G.points) := by
  classical
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hg)
  unfold subwordStepPoint simpleRepresentative
  simp only [inv_inv]
  split
  · exact G.isBruhatSystem.weyl.mem_normalizer _
  · split
    · exact Subgroup.one_mem _
    · exact Subgroup.inv_mem _ (G.isBruhatSystem.weyl.mem_normalizer _)

end SchubertGeometry
