import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupReducedWords
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupWeylQuotient
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.ParabolicSubgroup

/-! # Inverse simple representatives in the torus normalizer -/

noncomputable section
namespace ReductiveGroups
open TauCeti

private theorem word_inverse_reverse {ι A R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Group A]
    {P : RootPairing ι R M N} (b : P.Base) (f : ι → A) (l : List b.support) :
    simpleWordPoint (fun r => (f r)⁻¹) b l = (simpleWordPoint f b l.reverse)⁻¹ := by
  change (l.map (fun i : b.support => (f i.val)⁻¹)).prod =
    ((l.reverse.map (fun i : b.support => f i.val)).prod)⁻¹
  rw [List.prod_inv_reverse]
  simp only [List.reverse_reverse, List.map_reverse, List.map_map, Function.comp_def]

private theorem reduced_singleton {S W : Type*} [Group W] {M : CoxeterMatrix S}
    (cs : CoxeterSystem M W) (i : S) : cs.IsReduced [i] := by
  change cs.length (cs.simple i * 1) = 1
  rw [mul_one, cs.length_simple]

namespace ReductiveGroupData
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem representative_word (w : G.weylGroup) (l : List G.rootBase.support)
    (hl : (weylCoxeterSystem G.rootBase).IsReduced l)
    (hw : simpleWeylWord G.rootBase l = w) :
    weylElementPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase w =
      simpleWordPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase l := by
  exact G.invSimpleWordPoint_eq_of_reduced _ l (chosenReducedWord_isReduced G.rootBase w)
    hl ((simpleWeylWord_chosenReducedWord G.rootBase w).trans hw.symm)

private theorem representative_inv (w : G.weylGroup) :
    weylElementPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase w =
      (G.weylPoint w⁻¹)⁻¹ := by
  let l := chosenReducedWord G.rootBase w
  have hprod : simpleWeylWord G.rootBase l.reverse = w⁻¹ := by
    rw [simpleWeylWord_reverse, simpleWeylWord_chosenReducedWord]
  have he := G.simpleWordPoint_eq_of_reduced l.reverse (chosenReducedWord G.rootBase w⁻¹)
    (chosenReducedWord_isReduced G.rootBase w).reverse
    (chosenReducedWord_isReduced G.rootBase w⁻¹)
    (hprod.trans (simpleWeylWord_chosenReducedWord G.rootBase w⁻¹).symm)
  change simpleWordPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase l = _
  rw [word_inverse_reverse G.rootBase G.reflectionPoint l, he, G.weylPoint_eq]
  rfl

private theorem representative_class (w : G.weylGroup) :
    ∃ hw : weylElementPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
        G.rootBase w ∈ G.torusNormalizer,
      (QuotientGroup.mk (⟨weylElementPoint (fun r : G.rootIndex =>
        (G.reflectionPoint r)⁻¹) G.rootBase w, hw⟩ : G.torusNormalizer) :
        G.torusNormalizer ⧸ G.torusInNormalizer) = G.weylQuotientMap w := by
  have hn := G.torusNormalizer.inv_mem (G.weylPoint_mem_normalizer w⁻¹)
  have he := representative_inv G w
  refine ⟨he.symm ▸ hn, ?_⟩
  have hs : (⟨weylElementPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
        G.rootBase w, he.symm ▸ hn⟩ : G.torusNormalizer) =
      (⟨G.weylPoint w⁻¹, G.weylPoint_mem_normalizer w⁻¹⟩ : G.torusNormalizer)⁻¹ :=
    Subtype.ext he
  calc
    _ = (G.weylQuotientMap w⁻¹)⁻¹ := congrArg QuotientGroup.mk hs
    _ = G.weylQuotientMap w := by rw [map_inv, inv_inv]

/-- Inverse simple products give reduced-word representatives in the normalizer quotient. -/
theorem inverseRepresentative_properties :
    let rep : G.weylGroup → G.points :=
      weylElementPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase
    (∀ (w : G.weylGroup) (l : List G.rootBase.support),
      (weylCoxeterSystem G.rootBase).IsReduced l → simpleWeylWord G.rootBase l = w →
        rep w = simpleWordPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
          G.rootBase l) ∧
    rep 1 = 1 ∧
    (∀ i : G.rootBase.support,
      rep (RootPairing.weylGroup.ofIdx G.rootSystem i.val) = (G.reflectionPoint i.val)⁻¹) ∧
    ∀ w : G.weylGroup, ∃ hw : rep w ∈ G.torusNormalizer,
      (QuotientGroup.mk (⟨rep w, hw⟩ : G.torusNormalizer) :
        G.torusNormalizer ⧸ G.torusInNormalizer) = G.weylQuotientMap w := by
  refine ⟨representative_word G, weylElementPoint_one _ _, ?_, representative_class G⟩
  intro i
  rw [representative_word G (RootPairing.weylGroup.ofIdx G.rootSystem i.val) [i]
    (reduced_singleton (weylCoxeterSystem G.rootBase) i) (by simp [simpleWeylWord]),
    simpleWordPoint_singleton]

end ReductiveGroupData
end ReductiveGroups
