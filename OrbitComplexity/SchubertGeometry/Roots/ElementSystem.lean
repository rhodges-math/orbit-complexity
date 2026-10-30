import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupWeylQuotient
import OrbitComplexity.GroupActions.Varieties.SpecialLinear
import OrbitComplexity.SchubertGeometry.Roots.Subgroups

/-! # Systems of root elements and simple Weyl representatives -/

noncomputable section
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Simple matrix maps, root parameters and their contextual representatives. -/
def IsRootElementSystem
    (X Y : G.rootIndex → G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K) : Prop :=
  let dotw : G.weylGroup → G.points :=
    weylElementPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹) G.rootBase
  (∀ r, Y r = X (-r)) ∧
  (∀ r, gaAffineGroupTangent (X r) ∈ G.rootWeightSpace r ∧
    gaAffineGroupTangent (X r) ≠ 0 ∧ Function.Surjective (X r) ∧
    IsClosedImmersion (gaMorphism G (X r)).left ∧
    Set.range (fun a : K => gaParameterPoint (X r) a) =
      (rootSubgroupPoints G r : Set G.points)) ∧
  (∀ i : G.rootBase.support,
    X i.val = G.simpleRootMap i ∧ Y i.val = G.negativeSimpleRootMap i) ∧
  (∀ i : G.rootBase.support, IsMonHom (simpleSl2Morphism G i)) ∧
  (∀ (i : G.rootBase.support) (a : K),
    Variety.mapPoints (simpleSl2Morphism G i)
        (specialLinearPointsMulEquiv K 2 (Matrix.SpecialLinearGroup.transvection
          (zero_ne_one : (0 : Fin 2) ≠ 1) a)) =
      reductivePointsMulEquiv G (gaParameterPoint (X i.val) a)) ∧
  (∀ (i : G.rootBase.support) (a : K),
    Variety.mapPoints (simpleSl2Morphism G i)
        (specialLinearPointsMulEquiv K 2 (Matrix.SpecialLinearGroup.transvection
          (one_ne_zero : (1 : Fin 2) ≠ 0) a)) =
      reductivePointsMulEquiv G (gaParameterPoint (Y i.val) a)) ∧
  (∀ i : G.rootBase.support,
    Variety.mapPoints (simpleSl2Morphism G i)
        (specialLinearPointsMulEquiv K 2 (sl2Weyl K)) =
      reductivePointsMulEquiv G ((G.reflectionPoint i.val)⁻¹)) ∧
  (∀ (w : G.weylGroup) (l : List G.rootBase.support),
    (weylCoxeterSystem G.rootBase).IsReduced l → simpleWeylWord G.rootBase l = w →
      dotw w = simpleWordPoint (fun r : G.rootIndex => (G.reflectionPoint r)⁻¹)
        G.rootBase l) ∧
  dotw 1 = 1 ∧
  (∀ i : G.rootBase.support,
    dotw (RootPairing.weylGroup.ofIdx G.rootSystem i.val) = (G.reflectionPoint i.val)⁻¹) ∧
  (∀ w : G.weylGroup, ∃ hw : dotw w ∈ G.torusNormalizer,
    (QuotientGroup.mk (⟨dotw w, hw⟩ : G.torusNormalizer) :
      G.torusNormalizer ⧸ G.torusInNormalizer) = G.weylQuotientMap w) ∧
  (∀ r : G.rootIndex, ∃ (w : G.weylGroup) (i : G.rootBase.support),
    G.rootSystem.weylGroupToPerm w i.val = r) ∧
  (∀ (w : G.weylGroup) (i : G.rootBase.support),
    Set.range (fun a : K => dotw w * gaParameterPoint (X i.val) a * (dotw w)⁻¹) =
      (rootSubgroupPoints G (G.rootSystem.weylGroupToPerm w i.val) : Set G.points)) ∧
  (∀ (w : G.weylGroup) (i : G.rootBase.support),
    Set.range (fun a : K => dotw w * gaParameterPoint (Y i.val) a * (dotw w)⁻¹) =
      (rootSubgroupPoints G (-G.rootSystem.weylGroupToPerm w i.val) : Set G.points)) ∧
  (∀ (w : G.weylGroup) (i : G.rootBase.support),
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ a : K,
      (dotw w * gaParameterPoint (X i.val) a * (dotw w)⁻¹ =
        gaParameterPoint (X (G.rootSystem.weylGroupToPerm w i.val)) (ε * a)) ∧
      (dotw w * gaParameterPoint (Y i.val) a * (dotw w)⁻¹ =
        gaParameterPoint (Y (G.rootSystem.weylGroupToPerm w i.val)) (ε * a))) ∧
  ∀ (r : G.rootIndex) (ψ : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K),
    gaAffineGroupTangent ψ ∈ G.rootWeightSpace r → gaAffineGroupTangent ψ ≠ 0 →
    ∃ c : Kˣ, ∀ a : K, gaParameterPoint ψ a = gaParameterPoint (X r) ((c : K) * a)

end SchubertGeometry
