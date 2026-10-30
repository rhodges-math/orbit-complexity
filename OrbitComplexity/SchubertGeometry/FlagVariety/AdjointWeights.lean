import OrbitComplexity.SchubertGeometry.FlagVariety.AdjointOrbit
import OrbitComplexity.SchubertGeometry.Cells.Schubert
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.ExteriorWeights
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviCharacter
import OrbitComplexity.GroupActions.MomentMaps.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Batteries.Tactic.Lint

/-! # Exterior coordinates of Weyl flags

The Weyl representatives transport the Borel top exterior vector. Its torus character
is the product of the transported positive-root characters, and every nonzero coordinate
has that character.
-/

open CategoryTheory AlgebraicGeometry TauCeti ReductiveGroups GroupActions
open scoped BigOperators
noncomputable section
namespace SchubertGeometry
universe u v
attribute [local instance] Classical.propDecidable MvPolynomial.gradedAlgebra

private theorem representation_intertwine {K A V : Type*} [Field K] [Monoid A]
    [AddCommGroup V] [Module K V] (rho : Representation K A V)
    (a b c : A) (h : a * b = b * c) (v : V) :
    rho a (rho b v) = rho b (rho c v) := by
  rw [← Module.End.mul_apply, ← map_mul, h, map_mul, Module.End.mul_apply]

private theorem eval_prod_single {K M I : Type*} [CommSemiring K] [CommMonoid M]
    (q : MonoidAlgebra K M →ₐ[K] K) (s : Finset I) (chi : I → M) :
    (∏ i ∈ s, q (MonoidAlgebra.single (chi i) 1)) =
      q (MonoidAlgebra.single (∏ i ∈ s, chi i) 1) := by
  rw [← map_prod, MonoidAlgebra.prod_single]
  simp only [Finset.prod_const_one]

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
  (G : ReductiveGroupData K)

private theorem weyl_root_eval (n : G.weylGroup)
    (z z' : WithConv (MonoidAlgebra K G.characters →ₐ[K] K))
    (hc : AlgHom.mapDomain G.torusSplit z * G.weylPoint n =
      G.weylPoint n * AlgHom.mapDomain G.torusSplit z') (r : G.rootIndex) :
    z'.ofConv (MonoidAlgebra.single (G.rootCharacter r) 1) =
      z.ofConv (MonoidAlgebra.single
        (G.rootCharacter (G.rootSystem.weylGroupToPerm n r)) 1) := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (G.rootWeightSpace_ne_bot r)
  have hy : affineGroupAdjointRepresentation (G.weylPoint n) x ∈
      G.rootWeightSpace (G.rootSystem.weylGroupToPerm n r) := by
    rw [← G.weylPoint_rootWeightSpace n r]
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hy0 : affineGroupAdjointRepresentation (G.weylPoint n) x ≠ 0 := by
    intro hz
    exact hx0 ((affineGroupAdjointLieEquiv (G.weylPoint n)).injective
      (hz.trans (map_zero _).symm))
  have ha := representation_intertwine affineGroupAdjointRepresentation
    (AlgHom.mapDomain G.torusSplit z) (G.weylPoint n)
    (AlgHom.mapDomain G.torusSplit z') hc x
  rw [AffineGroupAdjoint.eq_character_of_mem_weight G.torusSplit
      (G.rootCharacter (G.rootSystem.weylGroupToPerm n r)) z _ hy,
    AffineGroupAdjoint.eq_character_of_mem_weight G.torusSplit
      (G.rootCharacter r) z' x hx, map_smul] at ha
  exact (smul_left_injective K hy0 ha).symm

/-- A Weyl translate of the Borel top vector has the transported positive-root character. -/
theorem adjoint_weyl_torus
    (w : ⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent)
    (hdet : ∀ (e : G.tangent ≃ₗ[K] G.tangent)
      (hB : G.borelTangent.toSubmodule.map e.toLinearMap = G.borelTangent.toSubmodule),
      exteriorPower.map (Module.finrank K G.borelTangent.toSubmodule) e.toLinearMap w =
        LinearMap.det (e.ofSubmodules G.borelTangent.toSubmodule
          G.borelTangent.toSubmodule hB).toLinearMap • w)
    (n : G.weylGroup) (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K)) :
    exteriorPower.map (Module.finrank K G.borelTangent.toSubmodule)
        (affineGroupAdjointRepresentation (AlgHom.mapDomain G.torusSplit z))
        (exteriorPower.map (Module.finrank K G.borelTangent.toSubmodule)
          (affineGroupAdjointRepresentation (G.weylPoint n)) w) =
      z.ofConv (MonoidAlgebra.single
        (∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
          G.rootCharacter (G.rootSystem.weylGroupToPerm n r)) 1) •
        exteriorPower.map (Module.finrank K G.borelTangent.toSubmodule)
          (affineGroupAdjointRepresentation (G.weylPoint n)) w := by
  classical
  have ht := mapDomain_mem_torusPoints G.torusIdeal G.torusSplit
    G.split_surjective G.split_eq_zero z
  have hconj : (G.weylPoint n)⁻¹ * AlgHom.mapDomain G.torusSplit z *
      G.weylPoint n ∈ G.torusPoints :=
    (Subgroup.mem_normalizer_iff''.mp (G.weylPoint_mem_normalizer n) _).mp ht
  obtain ⟨z', hz'⟩ := (mem_torusPoints_iff G.torusIdeal G.torusSplit
    G.split_surjective G.split_eq_zero _).mp hconj
  have hc : AlgHom.mapDomain G.torusSplit z * G.weylPoint n =
      G.weylPoint n * AlgHom.mapDomain G.torusSplit z' := by
    rw [← hz']
    group
  have hp : z'.ofConv (MonoidAlgebra.single G.positiveRootCharacter 1) =
      z.ofConv (MonoidAlgebra.single
        (∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
          G.rootCharacter (G.rootSystem.weylGroupToPerm n r)) 1) := by
    have hleft := @eval_prod_single K G.characters G.rootIndex inferInstance inferInstance
      z'.ofConv (Finset.univ.filter G.rootBase.IsPos) G.rootCharacter
    have hright := @eval_prod_single K G.characters G.rootIndex inferInstance inferInstance
      z.ofConv (Finset.univ.filter G.rootBase.IsPos)
      (fun r ↦ G.rootCharacter (G.rootSystem.weylGroupToPerm n r))
    have hmiddle :
        (∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
          z'.ofConv (MonoidAlgebra.single (G.rootCharacter r) 1)) =
        (∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
          z.ofConv (MonoidAlgebra.single
            (G.rootCharacter (G.rootSystem.weylGroupToPerm n r)) 1)) := by
      apply Finset.prod_congr rfl
      intro r _
      exact weyl_root_eval G n z z' hc r
    have hchar : G.positiveRootCharacter =
        ∏ r ∈ Finset.univ.filter G.rootBase.IsPos, G.rootCharacter r := by
      dsimp only [ReductiveGroupData.positiveRootCharacter]
      apply Finset.prod_congr
      · ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · intro r _
        rfl
    exact (congrArg (fun c : G.characters ↦ z'.ofConv (MonoidAlgebra.single c 1)) hchar).trans
      (hleft.symm.trans (hmiddle.trans hright))
  let rho := Representation.exteriorPower
    (affineGroupAdjointRepresentation (K := K) (B := G.coordinateAlgebra))
      (Module.finrank K G.borelTangent.toSubmodule)
  have h := representation_intertwine rho (AlgHom.mapDomain G.torusSplit z)
    (G.weylPoint n) (AlgHom.mapDomain G.torusSplit z') hc w
  change exteriorPower.map _ _ (exteriorPower.map _ _ w) =
    exteriorPower.map _ _ (exteriorPower.map _ _ w) at h
  rw [DeterminantSection.borelTop_torus G w hdet z', map_smul, hp] at h
  exact h

private theorem projectivePoint_eq {K ι : Type u} {V : Type v}
    [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (b : Module.Basis ι K V) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (h : v = w) :
    comoduleProjectivePoint b v hv = comoduleProjectivePoint b w hw := by
  cases h
  rfl

private theorem exterior_projective_smul
    {K H ι : Type u} {V : Type v} [Field K] [CharZero K]
    [CommRing H] [HopfAlgebra K H] [IsReduced H] [Algebra.FiniteType K H]
    [IsAlgClosed K] [AddCommGroup V] [Module K V] [Comodule K H V]
    [Fintype ι] [DecidableEq ι] (d : ℕ) (b : Module.Basis ι K (⋀[K]^d V))
    (w : ⋀[K]^d V) (hw : w ≠ 0) (e : V ≃ₗ[K] V)
    (g : WithConv (H →ₐ[K] K))
    (hg : Comodule.basePointsRepresentation (H := H) V g = e.toLinearMap)
    (hne : exteriorPower.map d e.toLinearMap w ≠ 0) :
    let := exteriorPowerComodule (K := K) (H := H) (V := V) d
    let := comoduleProjectiveAction (H := H) b
    affineGroupPointsMulEquiv K H g • comoduleProjectivePoint b w hw =
      comoduleProjectivePoint b (exteriorPower.map d e.toLinearMap w) hne := by
  let := exteriorPowerComodule (K := K) (H := H) (V := V) d
  let := comoduleProjectiveAction (H := H) b
  dsimp only
  have h := comoduleProjective_smul b g w hw
  have hvec : Comodule.basePointsRepresentation (H := H) (⋀[K]^d V) g w =
      exteriorPower.map d e.toLinearMap w := by
    rw [exteriorPower_basePoints, Representation.exteriorPower_apply, hg]
  have hnbase : Comodule.basePointsRepresentation (H := H) (⋀[K]^d V) g w ≠ 0 :=
    (LinearMap.GeneralLinearGroup.toLinearEquiv
      (Representation.asGroupHom
        (Comodule.basePointsRepresentation (H := H) (⋀[K]^d V)) g)).map_ne_zero_iff.mpr hw
  exact h.trans (@projectivePoint_eq K ι (⋀[K]^d V) inferInstance inferInstance
    inferInstance inferInstance b
    (Comodule.basePointsRepresentation (H := H) (⋀[K]^d V) g w)
    (exteriorPower.map d e.toLinearMap w) hnbase hne hvec)

/-- The image of a Weyl flag is represented by the Weyl translate of the same top vector. -/
theorem adjointFlag_weyl_point {ι : Type u} [iFin : Fintype ι] [iDecEq : DecidableEq ι]
    (b : Module.Basis ι K (⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent)) :
    let := affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)
    let := exteriorPowerComodule (K := K) (H := G.coordinateAlgebra) (V := G.tangent)
      (Module.finrank K G.borelTangent.toSubmodule)
    let : ModObj (reductiveVariety G).toOver (projectiveVariety K ι).toOver :=
      @comoduleProjectiveAction K G.coordinateAlgebra ι
        (⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent)
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance b
    ∀ (w : ⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent) (hw : w ≠ 0)
      (hB : ∀ g ∈ G.borelPoints, reductivePointsMulEquiv G g •
        comoduleProjectivePoint b w hw = comoduleProjectivePoint b w hw) (n : G.weylGroup),
      ∃ hn : exteriorPower.map (Module.finrank K G.borelTangent.toSubmodule)
          (affineGroupAdjointRepresentation (G.weylPoint n)) w ≠ 0,
        Variety.mapPoints
          (flagOrbitMorphism G (projectiveVariety K ι) (comoduleProjectivePoint b w hw) hB)
          (weylFlagPoint G n) = comoduleProjectivePoint b
            (exteriorPower.map (Module.finrank K G.borelTangent.toSubmodule)
              (affineGroupAdjointRepresentation (G.weylPoint n)) w) hn := by
  classical
  let := affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)
  let := exteriorPowerComodule (K := K) (H := G.coordinateAlgebra) (V := G.tangent)
    (Module.finrank K G.borelTangent.toSubmodule)
  let : ModObj (reductiveVariety G).toOver (projectiveVariety K ι).toOver :=
    @comoduleProjectiveAction K G.coordinateAlgebra ι
      (⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance b
  dsimp only
  intro w hw hB n
  have hn : exteriorPower.map (Module.finrank K G.borelTangent.toSubmodule)
      (affineGroupAdjointRepresentation (G.weylPoint n)) w ≠ 0 := by
    intro hz
    exact hw ((exteriorPower.map_injective_field
      (affineGroupAdjointLieEquiv (G.weylPoint n)).injective)
      (hz.trans (map_zero _).symm))
  have hsmul := @exterior_projective_smul K G.coordinateAlgebra ι G.tangent
    kField kZero inferInstance inferInstance inferInstance inferInstance kClosed
    inferInstance inferInstance (affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra))
    iFin iDecEq (Module.finrank K G.borelTangent.toSubmodule) b w hw
    (affineGroupAdjointLieEquiv (G.weylPoint n)).toLinearEquiv (G.weylPoint n)
    (affineGroupAdjointComodule_points (G.weylPoint n)) hn
  have hpoint := @flagOrbitMorphism_representative K kField kClosed kZero G
    (projectiveVariety K ι) inferInstance (comoduleProjectivePoint b w hw) hB (G.weylPoint n)
  have hp : reductivePointsMulEquiv G (G.weylPoint n) =
      affineGroupPointsMulEquiv K G.coordinateAlgebra (G.weylPoint n) := rfl
  rw [hp] at hpoint
  refine ⟨hn, ?_⟩
  exact (congrArg (Variety.mapPoints
    (flagOrbitMorphism G (projectiveVariety K ι) (comoduleProjectivePoint b w hw) hB))
      (show weylFlagPoint G n =
        flagVarietyPointsEquiv G (flagProjection G (G.weylPoint n)) from rfl)).trans
          (hpoint.trans hsmul)

private theorem exterior_basis_eigen {K M V I : Type*} [Field K] [CommGroup M]
    [AddCommGroup V] [Module K V] [LinearOrder I]
    (b : Module.Basis I K V) (chi : I → M) (q : MonoidAlgebra K M →ₐ[K] K)
    (f : V →ₗ[K] V) (hf : ∀ i, f (b i) = q (MonoidAlgebra.single (chi i) 1) • b i)
    (d : ℕ) (s : Set.powersetCard I d) :
    exteriorPower.map d f (b.exteriorPower d s) =
      q (MonoidAlgebra.single (∏ i ∈ s.val, chi i) 1) • b.exteriorPower d s := by
  have h := exteriorPower.map_basis_exteriorPower_of_apply_basis b f
    (fun i ↦ q (MonoidAlgebra.single (chi i) 1)) hf d s
  exact h.trans (congrArg (fun a : K ↦ a • b.exteriorPower d s)
    (@eval_prod_single K M I inferInstance inferInstance q s.val chi))

/-- A nonzero coordinate of a Weyl-flag vector has the transported positive-root character. -/
theorem adjoint_weyl_coordinate
    (w : ⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent)
    (hdet : ∀ (e : G.tangent ≃ₗ[K] G.tangent)
      (hB : G.borelTangent.toSubmodule.map e.toLinearMap = G.borelTangent.toSubmodule),
      exteriorPower.map (Module.finrank K G.borelTangent.toSubmodule) e.toLinearMap w =
        LinearMap.det (e.ofSubmodules G.borelTangent.toSubmodule
          G.borelTangent.toSubmodule hB).toLinearMap • w) (n : G.weylGroup) :
    let d := Module.finrank K G.borelTangent.toSubmodule
    let b := ((adjointWeightBasis G.torusSplit).exteriorPower d).reindex Equiv.ulift.symm
    ∀ s : ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d),
      b.equivFun (exteriorPower.map d (affineGroupAdjointRepresentation (G.weylPoint n)) w) s ≠ 0 →
        (∏ i ∈ s.down.val, adjointWeightCharacter G.torusSplit i) =
          ∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
            G.rootCharacter (G.rootSystem.weylGroupToPerm n r) := by
  classical
  let d := Module.finrank K G.borelTangent.toSubmodule
  let b := ((adjointWeightBasis G.torusSplit).exteriorPower d).reindex Equiv.ulift.symm
  let wt (s : ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)) :=
    ∏ i ∈ s.down.val, adjointWeightCharacter G.torusSplit i
  let rho := fun z : MonoidAlgebra K G.characters →ₐ[K] K ↦
    exteriorPower.map d
      (affineGroupAdjointRepresentation (AlgHom.mapDomain G.torusSplit (WithConv.toConv z)))
  have hdiag (z) (s) : rho z (b s) =
      z (MonoidAlgebra.single (wt s) (1 : K)) • b s := by
    have hbs := Module.Basis.reindex_apply
      ((adjointWeightBasis G.torusSplit).exteriorPower d) Equiv.ulift.symm s
    rw [hbs]
    exact @exterior_basis_eigen K G.characters G.tangent
      (Fin (adjointWeightRank G.torusSplit)) kField inferInstance inferInstance inferInstance
      inferInstance (adjointWeightBasis G.torusSplit) (adjointWeightCharacter G.torusSplit) z
      (affineGroupAdjointRepresentation (AlgHom.mapDomain G.torusSplit (WithConv.toConv z)))
      (adjointWeightBasis_torus G.torusSplit (WithConv.toConv z)) d s.down
  have hv (z) : rho z
        (exteriorPower.map d (affineGroupAdjointRepresentation (G.weylPoint n)) w) =
      z (MonoidAlgebra.single
        (∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
          G.rootCharacter (G.rootSystem.weylGroupToPerm n r)) 1) •
        exteriorPower.map d (affineGroupAdjointRepresentation (G.weylPoint n)) w :=
    adjoint_weyl_torus G w hdet n (WithConv.toConv z)
  dsimp only
  intro s hs
  by_contra hne
  have hcoords := congrFun (Module.Basis.equivFun_apply b
    (exteriorPower.map d (affineGroupAdjointRepresentation (G.weylPoint n)) w)) s
  exact hs (hcoords.trans (@DeterminantWeights.coordinate_vanishes_of_points K kField kClosed G
    (ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))
    (⋀[K]^d G.tangent) inferInstance inferInstance b wt rho hdiag
    (exteriorPower.map d (affineGroupAdjointRepresentation (G.weylPoint n)) w)
    (∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
      G.rootCharacter (G.rootSystem.weylGroupToPerm n r)) hv s hne))

private theorem point_polytope_singleton {I V E : Type} [Fintype I]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup E] [Module ℝ E]
    (b : Module.Basis I ℂ V) (weight : I → E) (v : V) (hv : v ≠ 0) (a : E)
    (h : ∀ i, b.equivFun v i ≠ 0 → weight i = a)
    (p : (projectiveVariety ℂ I).points) (hp : p = comoduleProjectivePoint b v hv) :
    weightPolytope weight (projectivePointsEquiv.symm p) = {a} ∧
      ∃ i, b.equivFun v i ≠ 0 ∧ (projectiveVariety ℂ I).pointMap p ∈
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule I ℂ) (MvPolynomial.X i) := by
  subst p
  have hn := b.equivFun.map_ne_zero_iff.mpr hv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
  refine ⟨?_, i, hi, ?_⟩
  · unfold comoduleProjectivePoint
    rw [Equiv.symm_apply_apply, weightPolytope_mk]
    have he : weight '' Function.support (b.equivFun v) = {a} := by
      apply Set.Subset.antisymm
      · rintro y ⟨j, hj, rfl⟩
        exact Set.mem_singleton_iff.mpr (h j hj)
      · intro y hy
        have hy' : y = a := Set.mem_singleton_iff.mp hy
        subst y
        exact ⟨i, hi, h i hi⟩
    rw [he, convexHull_singleton]
  · have ho := (@projectiveVectorPoint_basicOpen ℂ I inferInstance inferInstance
      (b.equivFun v) hn 1 Nat.zero_lt_one (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X ℂ i)).mpr
        (by simpa only [MvPolynomial.eval_X, Pi.zero_apply] using hi)
    simpa only [comoduleProjectivePoint, projectivePointsEquiv_mk] using ho

/-- The supported polytope of a Weyl flag is a singleton, and a coordinate of its character
is nonzero at the image point. -/
theorem adjointFlag_weightPolytope (G : ReductiveGroupData ℂ) :
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
    ∀ (w : ⋀[ℂ]^d G.tangent) (hw : w ≠ 0)
      (hB : ∀ g ∈ G.borelPoints, reductivePointsMulEquiv G g •
        comoduleProjectivePoint b w hw = comoduleProjectivePoint b w hw)
      (_hdet : ∀ (e : G.tangent ≃ₗ[ℂ] G.tangent)
        (hF : G.borelTangent.toSubmodule.map e.toLinearMap = G.borelTangent.toSubmodule),
        exteriorPower.map d e.toLinearMap w = LinearMap.det
          (e.ofSubmodules G.borelTangent.toSubmodule G.borelTangent.toSubmodule hF).toLinearMap • w)
      (z : G.weylGroup),
      weightPolytope
        (fun (s : ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)) j =>
          ((∏ i ∈ s.down.val, adjointWeightCharacter G.torusSplit i).toAdd j : ℝ))
        (projectivePointsEquiv.symm (Variety.mapPoints
          (flagOrbitMorphism G (projectiveVariety ℂ
            (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
            (comoduleProjectivePoint b w hw) hB) (weylFlagPoint G z))) =
        {fun j => ((∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
          G.rootCharacter (G.rootSystem.weylGroupToPerm z r)).toAdd j : ℝ)} ∧
      ∃ s : ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d),
        (∏ i ∈ s.down.val, adjointWeightCharacter G.torusSplit i) =
          (∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
            G.rootCharacter (G.rootSystem.weylGroupToPerm z r)) ∧
        (projectiveVariety ℂ
          (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))).pointMap
          (Variety.mapPoints (flagOrbitMorphism G (projectiveVariety ℂ
            (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
            (comoduleProjectivePoint b w hw) hB) (weylFlagPoint G z)) ∈
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule
            (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)) ℂ)
            (MvPolynomial.X s) := by
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
  dsimp only
  intro w hw hB hdet z
  have hImage := @adjointFlag_weyl_point ℂ inferInstance inferInstance inferInstance G
    (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))
    inferInstance inferInstance b w hw hB z
  obtain ⟨hn, himage⟩ := hImage
  have hchar := @adjoint_weyl_coordinate ℂ inferInstance inferInstance inferInstance G w hdet z
  obtain ⟨hP, s, hs, hopen⟩ := @point_polytope_singleton
    (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))
    (⋀[ℂ]^d G.tangent) (G.torusIndex → ℝ) inferInstance inferInstance inferInstance
    inferInstance inferInstance b
    (fun s j => ((∏ i ∈ s.down.val, adjointWeightCharacter G.torusSplit i).toAdd j : ℝ))
    (exteriorPower.map d (affineGroupAdjointRepresentation (G.weylPoint z)) w) hn
    (fun j => ((∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
      G.rootCharacter (G.rootSystem.weylGroupToPerm z r)).toAdd j : ℝ))
    (fun s hs => congrArg (fun c : G.characters => fun j => (c.toAdd j : ℝ)) (hchar s hs))
    (Variety.mapPoints (flagOrbitMorphism G (projectiveVariety ℂ
      (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
      (comoduleProjectivePoint b w hw) hB) (weylFlagPoint G z)) himage
  exact ⟨hP, s, hchar s hs, hopen⟩

end SchubertGeometry
