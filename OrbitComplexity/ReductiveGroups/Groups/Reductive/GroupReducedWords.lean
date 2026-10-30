import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupCommutingBraid
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBraidThree
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBraidFour
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSixBraid
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.WordProducts

/-! # Braid relations and reduced-word independence in reductive groups -/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open CoxeterSystem TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The fixed simple representatives satisfy every finite crystallographic braid. -/
theorem reflectionPoints_braid (i j : G.rootBase.support) :
    simpleWordPoint G.reflectionPoint G.rootBase
        (braidWord (simpleCoxeterMatrix G.rootBase) i j) =
      simpleWordPoint G.reflectionPoint G.rootBase
        (braidWord (simpleCoxeterMatrix G.rootBase) j i) := by
  by_cases hij : i = j
  · subst j
    rfl
  by_cases hz : simpleCoxeterMatrix G.rootBase i j = 0
  · simp only [simpleWordPoint, braidWord,
      (simpleCoxeterMatrix G.rootBase).symmetric j i, hz, alternatingWord,
      List.map_nil, List.prod_nil]
  have hc : simpleCoxeterMatrix G.rootBase i j =
      coxeterMatrixOfBase G.rootSystem G.rootBase i j :=
    (simpleCoxeterMatrix_apply G.rootBase i j).trans
      (RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase
        G.rootSystem G.rootBase i j)
  have hm := coxeterMatrixOfBase_mem_of_ne G.rootSystem G.rootBase hij
  rw [← hc] at hm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with hm | hm | hm | hm
  · have hp := (G.reflectionPoints_commute_of_order_two i j
      ((simpleCoxeterMatrix_apply G.rootBase i j).symm.trans hm)).eq
    simpa only [simpleWordPoint, braidWord,
      (simpleCoxeterMatrix G.rootBase).symmetric j i, hm, alternatingWord,
      List.concat_eq_append, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, one_mul, ← mul_assoc] using hp
  · have hp := G.reflectionPoints_braid_three i j
      ((simpleCoxeterMatrix_apply G.rootBase i j).symm.trans hm)
    simpa only [simpleWordPoint, braidWord,
      (simpleCoxeterMatrix G.rootBase).symmetric j i, hm, alternatingWord,
      List.concat_eq_append, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, one_mul, ← mul_assoc] using hp.symm
  · have hp := G.reflection_braid_of_order_four i j
      ((simpleCoxeterMatrix_apply G.rootBase i j).symm.trans hm)
    simpa only [simpleWordPoint, braidWord,
      (simpleCoxeterMatrix G.rootBase).symmetric j i, hm, alternatingWord,
      List.concat_eq_append, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, one_mul, ← mul_assoc] using hp
  · have hp := G.reflectionPoints_braid_six i j
      ((simpleCoxeterMatrix_apply G.rootBase i j).symm.trans hm)
    simpa only [simpleWordPoint, braidWord,
      (simpleCoxeterMatrix G.rootBase).symmetric j i, hm, alternatingWord,
      List.concat_eq_append, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, one_mul, ← mul_assoc] using hp

/-- Reduced words with the same Weyl element give the same fixed-representative product. -/
theorem simpleWordPoint_eq_of_reduced (l k : List G.rootBase.support)
    (hl : (weylCoxeterSystem G.rootBase).IsReduced l)
    (hk : (weylCoxeterSystem G.rootBase).IsReduced k)
    (heq : simpleWeylWord G.rootBase l = simpleWeylWord G.rootBase k) :
    simpleWordPoint G.reflectionPoint G.rootBase l =
      simpleWordPoint G.reflectionPoint G.rootBase k := by
  apply reduced_word_product_eq G.rootBase (fun i => G.reflectionPoint i.val)
  · intro i j _
    exact G.reflectionPoints_braid i j
  · exact hl
  · exact hk
  · simpa only [weylCoxeterSystem_wordProd] using heq

/-- Products of inverse fixed representatives are independent of a reduced Weyl word. -/
theorem invSimpleWordPoint_eq_of_reduced (l k : List G.rootBase.support)
    (hl : (weylCoxeterSystem G.rootBase).IsReduced l)
    (hk : (weylCoxeterSystem G.rootBase).IsReduced k)
    (heq : simpleWeylWord G.rootBase l = simpleWeylWord G.rootBase k) :
    simpleWordPoint (fun r => (G.reflectionPoint r)⁻¹) G.rootBase l =
      simpleWordPoint (fun r => (G.reflectionPoint r)⁻¹) G.rootBase k := by
  apply reduced_word_inv_product_eq G.rootBase (fun i => G.reflectionPoint i.val)
  · intro i j _
    exact G.reflectionPoints_braid i j
  · exact hl
  · exact hk
  · simpa only [weylCoxeterSystem_wordProd] using heq

end ReductiveGroups.ReductiveGroupData
