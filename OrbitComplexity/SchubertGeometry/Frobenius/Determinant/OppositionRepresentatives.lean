import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionRoots
import OrbitComplexity.SchubertGeometry.Deodhar.SimpleCell
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Representatives of opposition simple reflections

Conjugating an inverse simple representative by the longest representative
gives an inverse opposition-simple representative times a torus point.
The corresponding translated flag chart is centered at that simple Weyl flag.
-/

open ReductiveGroups GroupActions

namespace SchubertGeometry.DeterminantSection

noncomputable section

open private flagProjection_borel from
  OrbitComplexity.SchubertGeometry.FlagVariety.QuotientCharts

private theorem inverse_conjugate_factor {M : Type*} [Group M]
    (T : Subgroup M) (w f r n t u : M) (ht : t ∈ T) (hu : u ∈ T)
    (hconj : w * f * w⁻¹ = t * n) (hroot : r = u * n) :
    ∃ b ∈ T, w * f⁻¹ * w⁻¹ = r⁻¹ * b := by
  refine ⟨u * t⁻¹, T.mul_mem hu (T.inv_mem ht), ?_⟩
  have h : w * f * w⁻¹ = t * u⁻¹ * r := by
    calc
      _ = t * n := hconj
      _ = t * u⁻¹ * r := by rw [hroot]; group
  calc
    w * f⁻¹ * w⁻¹ = (w * f * w⁻¹)⁻¹ := by group
    _ = (t * u⁻¹ * r)⁻¹ := congrArg Inv.inv h
    _ = r⁻¹ * (u * t⁻¹) := by group

private theorem reflection_index_eq {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (w : P.weylGroup) (i j : ι)
    (h : P.root j = - (w • P.root i)) :
    P.reflectionPerm j j = P.weylGroupToPerm w i := by
  apply P.root.injective
  calc
    P.root (P.reflectionPerm j j) = - P.root j := by
      rw [P.root_reflectionPerm, P.reflection_apply_self]
    _ = - (- (w • P.root i)) := congrArg Neg.neg h
    _ = w • P.root i := neg_neg _
    _ = P.root (P.weylGroupToPerm w i) := P.weylGroup_apply_root w i

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
variable (G : ReductiveGroupData K)

/-- The longest action sends the negative of a simple root to its opposition simple root. -/
theorem oppositionSimple_index (i : G.rootBase.support) :
    G.rootSystem.weylGroupToPerm G.longestElement
      (G.rootSystem.reflectionPerm i.val i.val) = (oppositionSimple G i).val := by
  apply G.rootSystem.root.injective
  rw [← G.rootSystem.weylGroup_apply_root, G.rootSystem.root_reflectionPerm,
    G.rootSystem.reflection_apply_self, smul_neg, oppositionSimple_root]

private theorem opposition_negative_index (i : G.rootBase.support) :
    G.rootSystem.reflectionPerm (oppositionSimple G i).val (oppositionSimple G i).val =
      G.rootSystem.weylGroupToPerm G.longestElement i.val :=
  reflection_index_eq G.rootSystem G.longestElement i.val (oppositionSimple G i).val
    (oppositionSimple_root G i)

private theorem longest_transport :
    G.rootPointTransport G.longestPoint
      (G.rootSystem.weylGroupToPerm G.longestElement) := by
  change G.rootPointTransport (G.weylPoint G.longestElement) _
  rw [G.weylPoint_eq]
  exact G.isBruhatSystem.weyl.weylElementPoint_transport G.rootBase G.longestElement

/-- The group point translating the root-product chart toward its simple opposite boundary. -/
def oppositionChartPoint (i : G.rootBase.support) : G.points :=
  G.longestPoint * (G.reflectionPoint i.val)⁻¹ * G.longestPoint⁻¹

/-- The boundary chart representative differs from the specified inverse simple
representative by a torus point on its right. -/
theorem oppositionChartPoint_torus (i : G.rootBase.support) :
    ∃ b ∈ G.torusPoints,
      oppositionChartPoint G i = (G.reflectionPoint (oppositionSimple G i).val)⁻¹ * b := by
  obtain ⟨t, ht, hconj⟩ := G.isBruhatSystem.weyl.conj_mem G.longestPoint
    (G.rootSystem.weylGroupToPerm G.longestElement) G.longestPoint_mem_normalizer
    (longest_transport G) i.val
  obtain ⟨u, hu, hself⟩ := G.isBruhatSystem.weyl.conj_mem
    (G.reflectionPoint (oppositionSimple G i).val)
    (G.rootSystem.reflectionPerm (oppositionSimple G i).val)
    (G.isBruhatSystem.weyl.mem_normalizer (oppositionSimple G i).val)
    (G.isBruhatSystem.weyl.transport_reflection (oppositionSimple G i).val)
    (oppositionSimple G i).val
  have hroot : G.reflectionPoint (oppositionSimple G i).val =
      u * G.reflectionPoint (G.rootSystem.weylGroupToPerm G.longestElement i.val) := by
    calc
      _ = G.reflectionPoint (oppositionSimple G i).val *
          G.reflectionPoint (oppositionSimple G i).val *
            (G.reflectionPoint (oppositionSimple G i).val)⁻¹ := by group
      _ = u * G.reflectionPoint
          (G.rootSystem.reflectionPerm (oppositionSimple G i).val
            (oppositionSimple G i).val) := hself
      _ = _ := congrArg (fun r => u * G.reflectionPoint r) (opposition_negative_index G i)
  exact inverse_conjugate_factor G.torusPoints G.longestPoint (G.reflectionPoint i.val)
    (G.reflectionPoint (oppositionSimple G i).val)
    (G.reflectionPoint (G.rootSystem.weylGroupToPerm G.longestElement i.val))
    t u ht hu hconj hroot

/-- The translated boundary chart has the opposition simple Weyl flag as its center. -/
theorem oppositionChartPoint_flag (i : G.rootBase.support) :
    flagProjection G (oppositionChartPoint G i) =
      flagProjection G (G.weylPoint
        (RootPairing.weylGroup.ofIdx G.rootSystem (oppositionSimple G i))) := by
  obtain ⟨b, hb, hpoint⟩ := oppositionChartPoint_torus G i
  calc
    _ = flagProjection G ((G.reflectionPoint (oppositionSimple G i).val)⁻¹ * b) :=
      congrArg (flagProjection G) hpoint
    _ = flagProjection G (G.reflectionPoint (oppositionSimple G i).val)⁻¹ :=
      flagProjection_borel G _ ⟨b, G.torus_le_borel hb⟩
    _ = _ := simpleRepresentative_flag G (oppositionSimple G i)

end

end SchubertGeometry.DeterminantSection
