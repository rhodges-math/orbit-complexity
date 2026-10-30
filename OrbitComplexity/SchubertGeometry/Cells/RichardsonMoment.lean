import OrbitComplexity.SchubertGeometry.Cells.RichardsonOrder
import OrbitComplexity.SchubertGeometry.Cells.RichardsonIntegral
import OrbitComplexity.SchubertGeometry.FlagVariety.MomentMap
import OrbitComplexity.SchubertGeometry.FlagVariety.AdjointWeights
import OrbitComplexity.GroupActions.MomentMaps.OrbitFaces
import OrbitComplexity.GroupActions.Actions.EquivariantMono
import OrbitComplexity.BruhatIntervals.Graph.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Batteries.Tactic.Lint

/-! # Supported polytopes on Richardson varieties

Fixed-point labels and proper orbit-closure lifting bound supported weights by
the convex hull of Bruhat interval weights.

## References

* E. Tsukerman and L. Williams, *Bruhat interval polytopes*, Adv. Math. 285 (2015), 766–810,
  Remark 7.11.
-/

open CategoryTheory AlgebraicGeometry TauCeti ReductiveGroups GroupActions BruhatIntervals
open Multiplicative
open scoped BigOperators
namespace SchubertGeometry
noncomputable section
attribute [local instance] Classical.propDecidable MvPolynomial.gradedAlgebra

private theorem richardson_polytope_subset {I : Type} {E : Type*} [iFin : Fintype I]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    (G : ReductiveGroupData ℂ) (weight : I → E)
    (f : (flagVariety G).toOver ⟶ (projectiveVariety ℂ I).toOver)
    (fixedWeight : G.weylGroup → E)
    (hSingleton : ∀ (x : (flagVariety G).points) (q : E),
      weightPolytope weight (projectivePointsEquiv.symm (Variety.mapPoints f x)) = {q} →
        ∀ t : (torusVariety G).points, t • x = x)
    (hFace : ∀ (x : (flagVariety G).points) (F : Set E), F.Nonempty →
      IsExposed ℝ (weightPolytope weight
        (projectivePointsEquiv.symm (Variety.mapPoints f x))) F →
      ∃ y : (flagVariety G).points,
        (flagVariety G).pointMap y ∈ orbitClosure (torusVariety G) (flagVariety G) x ∧
        weightPolytope weight (projectivePointsEquiv.symm (Variety.mapPoints f y)) = F)
    (hWeyl : ∀ z : G.weylGroup,
      weightPolytope weight (projectivePointsEquiv.symm
        (Variety.mapPoints f (weylFlagPoint G z))) = {fixedWeight z})
    (a b : G.weylGroup) :
    ∀ x : (richardsonVariety G a b).points,
      weightPolytope weight (projectivePointsEquiv.symm
        (Variety.mapPoints (richardsonInclusion G a b ≫ f) x)) ⊆
      convexHull ℝ (fixedWeight '' bruhatInterval (weylCoxeterSystem G.rootBase) a b) := by
  classical
  let fR := richardsonInclusion G a b ≫ f
  let P := fun x : (flagVariety G).points =>
    weightPolytope weight (projectivePointsEquiv.symm (Variety.mapPoints f x))
  let PR := fun x : (richardsonVariety G a b).points =>
    weightPolytope weight (projectivePointsEquiv.symm (Variety.mapPoints fR x))
  let Q := convexHull ℝ
    (fixedWeight '' bruhatInterval (weylCoxeterSystem G.rootBase) a b)
  have hPR (x : (richardsonVariety G a b).points) :
      PR x = P (Variety.mapPoints (richardsonInclusion G a b) x) := by
    dsimp only [PR, P, fR]
    rw [Variety.mapPoints_comp]
  change ∀ x : (richardsonVariety G a b).points, PR x ⊆ Q
  refine @weightPolytope_subset_of_fixed I E (richardsonVariety G a b).points
    iFin inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance weight
    (fun x => projectivePointsEquiv.symm (Variety.mapPoints fR x))
    (fun x => ∀ t : (torusVariety G).points, t • x = x) Q
    (convex_convexHull ℝ _) ?_ ?_ ?_
  · intro x q hq t
    apply Variety.mapPoints_injective_of_mono (richardsonInclusion G a b)
    rw [richardson_torus_smul]
    apply hSingleton (Variety.mapPoints (richardsonInclusion G a b) x) q
    change P (Variety.mapPoints (richardsonInclusion G a b) x) = {q}
    rw [← hPR]
    exact hq
  · intro x hx
    obtain ⟨z, haz, hzb, hz⟩ := (richardson_torus_fixed_iff G a b x).mp hx
    change PR x ⊆ Q
    rw [hPR, hz]
    change weightPolytope weight
      (projectivePointsEquiv.symm (Variety.mapPoints f (weylFlagPoint G z))) ⊆ Q
    rw [hWeyl]
    apply Set.singleton_subset_iff.mpr
    apply subset_convexHull ℝ _
    refine ⟨z, ?_, rfl⟩
    exact ⟨(weyl_bruhat_iff G.rootBase a z).mp haz,
      (weyl_bruhat_iff G.rootBase z b).mp hzb⟩
  · intro x F hFne hF
    have hF' : IsExposed ℝ
        (P (Variety.mapPoints (richardsonInclusion G a b) x)) F := by
      rw [← hPR]
      exact hF
    obtain ⟨y, hy, hPy⟩ := hFace
      (Variety.mapPoints (richardsonInclusion G a b) x) F hFne hF'
    have hLift := @orbitClosure_points_image ℂ inferInstance (torusVariety G)
      (richardsonVariety G a b) (flagVariety G)
      inferInstance inferInstance inferInstance inferInstance
      (richardsonInclusion G a b) inferInstance inferInstance x
    have hyLift : y ∈ Variety.mapPoints (richardsonInclusion G a b) ''
        {p : (richardsonVariety G a b).points | (richardsonVariety G a b).pointMap p ∈
          orbitClosure (torusVariety G) (richardsonVariety G a b) x} := by
      rw [hLift]
      exact hy
    obtain ⟨p, _hp, hp⟩ := hyLift
    refine ⟨p, ?_⟩
    change PR p = F
    rw [hPR, hp]
    exact hPy

private theorem richardson_polytope_point {I : Type} {E : Type*} [Finite I]
    [AddCommGroup E] [Module ℝ E]
    (G : ReductiveGroupData ℂ) (weight : I → E)
    (f : (flagVariety G).toOver ⟶ (projectiveVariety ℂ I).toOver)
    (fixedWeight : G.weylGroup → E)
    (hWeyl : ∀ z : G.weylGroup,
      weightPolytope weight (projectivePointsEquiv.symm
        (Variety.mapPoints f (weylFlagPoint G z))) = {fixedWeight z})
    (a b : G.weylGroup) (hab : WeylBruhatLE G.rootBase a b) :
    ∃ x : (richardsonVariety G a b).points,
      (∀ i : I, (∃ y : (richardsonVariety G a b).points,
        (projectiveVariety ℂ I).pointMap
          (Variety.mapPoints (richardsonInclusion G a b ≫ f) y) ∈
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule I ℂ) (MvPolynomial.X i)) →
        (projectiveVariety ℂ I).pointMap
          (Variety.mapPoints (richardsonInclusion G a b ≫ f) x) ∈
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule I ℂ) (MvPolynomial.X i)) ∧
      convexHull ℝ (fixedWeight '' bruhatInterval (weylCoxeterSystem G.rootBase) a b) ⊆
        weightPolytope weight (projectivePointsEquiv.symm
          (Variety.mapPoints (richardsonInclusion G a b ≫ f) x)) := by
  classical
  let fR := richardsonInclusion G a b ≫ f
  let PR := fun x : (richardsonVariety G a b).points =>
    weightPolytope weight (projectivePointsEquiv.symm (Variety.mapPoints fR x))
  have hMax := @richardson_maximal_weightPolytope G a b hab I E
    inferInstance inferInstance inferInstance fR weight
  obtain ⟨x, hCoordinates, hx⟩ := hMax
  refine ⟨x, hCoordinates, convexHull_min ?_ ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hzNative : WeylBruhatLE G.rootBase a z ∧ WeylBruhatLE G.rootBase z b :=
      ⟨(weyl_bruhat_iff G.rootBase a z).mpr hz.1,
        (weyl_bruhat_iff G.rootBase z b).mpr hz.2⟩
    obtain ⟨y, hy⟩ := (weylFlag_mem_richardson_iff G a b z).mpr hzNative
    apply hx y
    change fixedWeight z ∈ PR y
    have hPy : PR y = {fixedWeight z} := by
      dsimp only [PR, fR]
      rw [Variety.mapPoints_comp, hy]
      exact hWeyl z
    rw [hPy]
    exact Set.mem_singleton _
  · refine Projectivization.ind ?_
      (projectivePointsEquiv.symm (Variety.mapPoints fR x))
    intro v hv
    rw [weightPolytope_mk]
    exact convex_convexHull ℝ _


/-- Remark 7.11 of Tsukerman–Williams, with a general point in place of the totally positive
point of their Lemma 7.9: one adjoint moment map sends every Richardson variety onto the interval
weight hull, and one Richardson point has all interval weights in its nonzero coordinates. -/
theorem exists_richardson_moment_map (G : ReductiveGroupData ℂ) :
    let d := Module.finrank ℂ G.borelTangent.toSubmodule
    let b := ((adjointWeightBasis G.torusSplit).exteriorPower d).reindex Equiv.ulift.symm
    let := affineGroupAdjointComodule (K := ℂ) (B := G.coordinateAlgebra)
    let := exteriorPowerComodule (K := ℂ) (H := G.coordinateAlgebra) (V := G.tangent) d
    let : ModObj (reductiveVariety G).toOver (projectiveVariety ℂ
        (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))).toOver :=
      @comoduleProjectiveAction ℂ G.coordinateAlgebra
        (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)) (⋀[ℂ]^d G.tangent)
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance b
    ∃ (w : ⋀[ℂ]^d G.tangent) (hw : w ≠ 0)
      (hB : ∀ g ∈ G.borelPoints, reductivePointsMulEquiv G g •
        comoduleProjectivePoint b w hw = comoduleProjectivePoint b w hw),
      (∀ (e : G.tangent ≃ₗ[ℂ] G.tangent)
        (hF : G.borelTangent.toSubmodule.map e.toLinearMap = G.borelTangent.toSubmodule),
        exteriorPower.map d e.toLinearMap w =
          LinearMap.det (e.ofSubmodules G.borelTangent.toSubmodule
            G.borelTangent.toSubmodule hF).toLinearMap • w) ∧
      let f := flagOrbitMorphism G (projectiveVariety ℂ
        (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
        (comoduleProjectivePoint b w hw) hB
      let chi := fun s : ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d) =>
        toAdd (∏ i ∈ s.down.val, adjointWeightCharacter G.torusSplit i)
      let P := fun x : (flagVariety G).points =>
        weightPolytope (fun i j => (chi i j : ℝ))
          (projectivePointsEquiv.symm (Variety.mapPoints f x))
      let fixedWeight := fun z : G.weylGroup => fun j =>
        (((∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
          G.rootCharacter (G.rootSystem.weylGroupToPerm z r)).toAdd) j : ℝ)
      let Q := fun a b => convexHull ℝ
        (fixedWeight '' bruhatInterval (weylCoxeterSystem G.rootBase) a b)
      (∀ z : G.weylGroup, P (weylFlagPoint G z) = {fixedWeight z}) ∧
      (∀ x : (flagVariety G).points,
        orbitDim (torusVariety G) (flagVariety G) x =
          WithBot.map (fun n : ℕ => (n : ℕ∞)) (affineSpan ℝ (P x)).finDim) ∧
      ∀ a b : G.weylGroup, WeylBruhatLE G.rootBase a b →
        (∀ x : (richardsonVariety G a b).points,
          P (Variety.mapPoints (richardsonInclusion G a b) x) ⊆ Q a b) ∧
        (∃ x : (richardsonVariety G a b).points,
          P (Variety.mapPoints (richardsonInclusion G a b) x) = Q a b ∧
          (∀ z ∈ bruhatInterval (weylCoxeterSystem G.rootBase) a b,
            ∃ s : ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d),
              chi s = toAdd (∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
                G.rootCharacter (G.rootSystem.weylGroupToPerm z r)) ∧
              (projectiveVariety ℂ
                (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))).pointMap
                (Variety.mapPoints f (Variety.mapPoints (richardsonInclusion G a b) x)) ∈
                  Proj.basicOpen (MvPolynomial.homogeneousSubmodule
                    (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)) ℂ)
                    (MvPolynomial.X s)) ∧
          (fun y : (richardsonVariety G a b).points => flagMomentMap G w hw hB
            (Variety.mapPoints (richardsonInclusion G a b) y)) ''
              {y : (richardsonVariety G a b).points |
                (richardsonVariety G a b).pointMap y ∈
                  orbitClosure (torusVariety G) (richardsonVariety G a b) x} = Q a b) ∧
        Set.range (fun x : (richardsonVariety G a b).points =>
          flagMomentMap G w hw hB (Variety.mapPoints (richardsonInclusion G a b) x)) =
            Q a b := by
  classical
  let d := Module.finrank ℂ G.borelTangent.toSubmodule
  let b := ((adjointWeightBasis G.torusSplit).exteriorPower d).reindex Equiv.ulift.symm
  let := affineGroupAdjointComodule (K := ℂ) (B := G.coordinateAlgebra)
  let := exteriorPowerComodule (K := ℂ) (H := G.coordinateAlgebra) (V := G.tangent) d
  let : ModObj (reductiveVariety G).toOver (projectiveVariety ℂ
      (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))).toOver :=
    @comoduleProjectiveAction ℂ G.coordinateAlgebra
      (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)) (⋀[ℂ]^d G.tangent)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance b
  have hFlag := @exists_flag_moment_map G
  obtain ⟨w, hw, hB, hdet, _hEq, _hInject, hMoments⟩ := hFlag
  let f := flagOrbitMorphism G (projectiveVariety ℂ
    (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
    (comoduleProjectivePoint b w hw) hB
  let chi := fun s : ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d) =>
    toAdd (∏ i ∈ s.down.val, adjointWeightCharacter G.torusSplit i)
  let P := fun x : (flagVariety G).points =>
    weightPolytope (fun i j => (chi i j : ℝ))
      (projectivePointsEquiv.symm (Variety.mapPoints f x))
  let fixedWeight := fun z : G.weylGroup => fun j =>
    (((∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
      G.rootCharacter (G.rootSystem.weylGroupToPerm z r)).toAdd) j : ℝ)
  let Q := fun a b => convexHull ℝ
    (fixedWeight '' bruhatInterval (weylCoxeterSystem G.rootBase) a b)
  have hWeyl (z : G.weylGroup) : P (weylFlagPoint G z) = {fixedWeight z} := by
    exact (adjointFlag_weightPolytope G w hw hB hdet z).1
  refine ⟨w, hw, hB, hdet, hWeyl, ?_, ?_⟩
  · intro x
    exact (hMoments x).2.2.1
  · intro a b hab
    have hSub' := @richardson_polytope_subset
      (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))
      (G.torusIndex → ℝ) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance G
      (fun i j => (chi i j : ℝ)) f fixedWeight
      (fun x q hq => (hMoments x).2.2.2.2 q hq)
      (fun x F hF hEx => (hMoments x).2.2.2.1 F hF hEx) hWeyl a b
    have hSub : ∀ x : (richardsonVariety G a b).points,
        P (Variety.mapPoints (richardsonInclusion G a b) x) ⊆ Q a b := by
      simpa only [Variety.mapPoints_comp] using hSub'
    have hLower := @richardson_polytope_point
      (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))
      (G.torusIndex → ℝ) inferInstance inferInstance inferInstance G
      (fun i j => (chi i j : ℝ)) f fixedWeight hWeyl a b hab
    obtain ⟨xGen, hCoordinates, hxGen⟩ := hLower
    have hGen : P (Variety.mapPoints (richardsonInclusion G a b) xGen) = Q a b := by
      apply Set.Subset.antisymm (hSub xGen)
      simpa only [Variety.mapPoints_comp] using hxGen
    have hLift := @orbitClosure_points_image ℂ inferInstance (torusVariety G)
      (richardsonVariety G a b) (flagVariety G)
      inferInstance inferInstance inferInstance inferInstance
      (richardsonInclusion G a b) inferInstance inferInstance xGen
    have hClosure : (fun y : (richardsonVariety G a b).points => flagMomentMap G w hw hB
        (Variety.mapPoints (richardsonInclusion G a b) y)) ''
          {y : (richardsonVariety G a b).points |
            (richardsonVariety G a b).pointMap y ∈
              orbitClosure (torusVariety G) (richardsonVariety G a b) xGen} = Q a b := by
      rw [← Set.image_image, hLift]
      exact ((hMoments (Variety.mapPoints (richardsonInclusion G a b) xGen)).2.1).trans hGen
    refine ⟨hSub, ⟨xGen, hGen, ?_, hClosure⟩, ?_⟩
    · intro z hz
      obtain ⟨s, hs, hsOpen⟩ := (adjointFlag_weightPolytope G w hw hB hdet z).2
      obtain ⟨y, hy⟩ := (weylFlag_mem_richardson_iff G a b z).mpr
        ⟨(weyl_bruhat_iff G.rootBase a z).mpr hz.1,
          (weyl_bruhat_iff G.rootBase z b).mpr hz.2⟩
      refine ⟨s, congrArg toAdd hs, ?_⟩
      have hyOpen : (projectiveVariety ℂ
          (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))).pointMap
          (Variety.mapPoints (richardsonInclusion G a b ≫ f) y) ∈
            Proj.basicOpen (MvPolynomial.homogeneousSubmodule
              (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)) ℂ)
              (MvPolynomial.X s) := by
        rw [Variety.mapPoints_comp, hy]
        exact hsOpen
      have hxOpen := hCoordinates s ⟨y, hyOpen⟩
      simpa only [Variety.mapPoints_comp] using hxOpen
    · ext q
      constructor
      · rintro ⟨x, rfl⟩
        apply hSub x
        exact momentMap_mem_weightPolytope (fun i j => (chi i j : ℝ))
          (projectivePointsEquiv.symm (Variety.mapPoints f
            (Variety.mapPoints (richardsonInclusion G a b) x)))
      · intro hq
        change q ∈ Q a b at hq
        rw [← hClosure] at hq
        obtain ⟨y, _hy, hval⟩ := hq
        exact ⟨y, hval⟩

end
end SchubertGeometry
