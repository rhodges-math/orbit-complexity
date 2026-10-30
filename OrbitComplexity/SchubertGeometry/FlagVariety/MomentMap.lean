import OrbitComplexity.GroupActions.MomentMaps.OrbitFaces
import OrbitComplexity.GroupActions.Tori.ProjectiveWeights
import OrbitComplexity.GroupActions.Actions.EquivariantMono
import OrbitComplexity.SchubertGeometry.Cells.Stability
import OrbitComplexity.SchubertGeometry.FlagVariety.AdjointOrbit
import Batteries.Tactic.Lint

/-! # Moment images of torus orbits on flag varieties

The adjoint exterior embedding computes flag moment images from its character coordinates.
Properness lifts projective orbit-closure points to points of the flag orbit closure.

## References

* E. Tsukerman and L. Williams, *Bruhat interval polytopes*, Adv. Math. 285 (2015), 766–810,
  Theorem 6.19.
-/

open CategoryTheory AlgebraicGeometry TauCeti ReductiveGroups GroupActions Multiplicative
open scoped BigOperators
noncomputable section
namespace SchubertGeometry
attribute [local instance] Classical.propDecidable

private theorem torus_projective_moment {I V : Type} [Fintype I] [DecidableEq I]
    (G : ReductiveGroupData ℂ) [AddCommGroup V] [Module ℂ V]
    [Comodule ℂ G.coordinateAlgebra V] (b : Module.Basis I ℂ V)
    (chi : I → G.torusIndex →₀ ℤ)
    (hb : ∀ i, b i ∈ DiagonalizableGroup.weightSpace V G.torusSplit.toCoalgHom
      (ofAdd (chi i))) :
    let : ModObj (reductiveVariety G).toOver (projectiveVariety ℂ I).toOver :=
      @comoduleProjectiveAction ℂ G.coordinateAlgebra I V
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance b
    let := Mod.scalarRestriction (torusInclusion G) (projectiveVariety ℂ I).toOver
    let mu := fun p : (projectiveVariety ℂ I).points =>
      momentMap (fun i j => (chi i j : ℝ)) (projectivePointsEquiv.symm p)
    let P := fun p : (projectiveVariety ℂ I).points =>
      weightPolytope (fun i j => (chi i j : ℝ)) (projectivePointsEquiv.symm p)
    ∀ p : (projectiveVariety ℂ I).points,
      mu '' MulAction.orbit (torusVariety G).points p = intrinsicInterior ℝ (P p) ∧
      mu '' {q | (projectiveVariety ℂ I).pointMap q ∈
        orbitClosure (torusVariety G) (projectiveVariety ℂ I) p} = P p ∧
      orbitDim (torusVariety G) (projectiveVariety ℂ I) p =
        WithBot.map (fun n : ℕ => (n : ℕ∞)) (affineSpan ℝ (P p)).finDim ∧
      (∀ F : Set (G.torusIndex → ℝ), F.Nonempty → IsExposed ℝ (P p) F →
        ∃ q : (projectiveVariety ℂ I).points,
          (projectiveVariety ℂ I).pointMap q ∈
            orbitClosure (torusVariety G) (projectiveVariety ℂ I) p ∧ P q = F) ∧
      ∀ q : G.torusIndex → ℝ, P p = {q} → ∀ t : (torusVariety G).points, t • p = p := by
  classical
  let : Fintype G.torusIndex := Fintype.ofFinite G.torusIndex
  let : ModObj (reductiveVariety G).toOver (projectiveVariety ℂ I).toOver :=
    @comoduleProjectiveAction ℂ G.coordinateAlgebra I V
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance b
  let := Mod.scalarRestriction (torusInclusion G) (projectiveVariety ℂ I).toOver
  let mu := fun p : (projectiveVariety ℂ I).points =>
    momentMap (fun i j => (chi i j : ℝ)) (projectivePointsEquiv.symm p)
  let P := fun p : (projectiveVariety ℂ I).points =>
    weightPolytope (fun i j => (chi i j : ℝ)) (projectivePointsEquiv.symm p)
  dsimp only
  intro p
  obtain ⟨q, rfl⟩ := (projectivePointsEquiv (K := ℂ) (ι := I)).surjective p
  induction q using Projectivization.ind with
  | _ v hv =>
    have hvec : b.equivFun.symm v ≠ 0 := b.equivFun.symm.map_ne_zero_iff.mpr hv
    have hpoint : comoduleProjectivePoint b (b.equivFun.symm v) hvec =
        projectiveVectorPoint v hv := by
      simp only [comoduleProjectivePoint, LinearEquiv.apply_symm_apply,
        projectivePointsEquiv_mk]
    have hOrbit := @torus_projective_orbit ℂ I V inferInstance inferInstance
      inferInstance inferInstance G inferInstance inferInstance inferInstance
      b chi hb (b.equivFun.symm v) hvec
    have hClosure := @torus_projective_closure ℂ I V inferInstance inferInstance
      inferInstance inferInstance G inferInstance inferInstance inferInstance
      b chi hb (b.equivFun.symm v) hvec
    rw [hpoint] at hOrbit hClosure
    let : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (G.torusIndex →₀ ℤ))) (I → ℂ) :=
      Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (chi i))
    let := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (G.torusIndex →₀ ℤ)))
      I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun ℂ I)
    have hpacket := @projective_moment_faces I G.torusIndex inferInstance inferInstance
      inferInstance chi v hv
    obtain ⟨e, he, hclosed, hrest⟩ := hpacket
    have hP : P (projectiveVectorPoint v hv) =
        weightPolytope (fun i j => (chi i j : ℝ)) (Projectivization.mk ℂ v hv) := by
      change weightPolytope _
        (projectivePointsEquiv.symm (projectivePointsEquiv (Projectivization.mk ℂ v hv))) = _
      rw [Equiv.symm_apply_apply]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change mu '' MulAction.orbit (torusVariety G).points
        (projectiveVectorPoint v hv) = _
      rw [hOrbit]
      change mu '' Set.range (fun t : (affineVariety ℂ
        (MonoidAlgebra ℂ (Multiplicative (G.torusIndex →₀ ℤ)))).points =>
          t • projectiveVectorPoint v hv) = _
      rw [← Set.range_comp]
      exact (hrest (projectiveVectorPoint v hv)).1
    · change mu '' {q | (projectiveVariety ℂ I).pointMap q ∈
        orbitClosure (torusVariety G) (projectiveVariety ℂ I)
          (projectiveVectorPoint v hv)} = _
      refine (congrArg (fun S : Set (projectiveVariety ℂ I).scheme =>
        mu '' {q | (projectiveVariety ℂ I).pointMap q ∈ S}) hClosure).trans
          (Eq.trans ?_ hP.symm)
      apply Set.Subset.antisymm
      · rintro z ⟨r, hr, rfl⟩
        have hr' : (projectiveVariety ℂ I).pointMap
            (projectivePointsEquiv (projectivePointsEquiv.symm r)) ∈
            orbitClosure (affineVariety ℂ
              (MonoidAlgebra ℂ (Multiplicative (G.torusIndex →₀ ℤ))))
              (projectiveVariety ℂ I) (projectiveVectorPoint v hv) := by
          simpa only [Equiv.apply_symm_apply, Set.mem_ofPred_eq] using hr
        rw [← hclosed]
        exact ⟨⟨projectivePointsEquiv.symm r, hr'⟩, rfl⟩
      · intro z hz
        rw [← hclosed] at hz
        obtain ⟨r, hr⟩ := hz
        refine ⟨projectivePointsEquiv r.val, r.property, ?_⟩
        simpa only [mu, Equiv.symm_apply_apply] using hr
    · have hd := congrArg (fun S => (projectiveVariety ℂ I).subsetDim S) hOrbit
      exact hd.trans (hrest (projectiveVectorPoint v hv)).2
    · intro F hne hF
      have hF' : IsExposed ℝ
          (weightPolytope (fun i j => (chi i j : ℝ)) (Projectivization.mk ℂ v hv)) F := by
        rwa [← hP]
      obtain ⟨r, hr⟩ := e.surjective ⟨F, hne, hF'⟩
      obtain ⟨s, rfl⟩ := Quotient.exists_rep r
      refine ⟨s.val, ?_, (he s).symm.trans (congrArg Subtype.val hr)⟩
      exact Eq.mp (congrArg (fun S : Set (projectiveVariety ℂ I).scheme =>
        (projectiveVariety ℂ I).pointMap s.val ∈ S) hClosure.symm) s.property
    · intro q hq t
      have hfix := @projective_fixed_of_singleton I G.torusIndex inferInstance inferInstance
        inferInstance chi (projectiveVectorPoint v hv) q hq
      have hfixed : projectiveVectorPoint v hv ∈ MulAction.fixedPoints
          (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (G.torusIndex →₀ ℤ)))).points
          (projectiveVariety ℂ I).points := MulAction.mem_fixedPoints.mpr hfix
      have hmem0 : t • projectiveVectorPoint v hv ∈
          MulAction.orbit (torusVariety G).points (projectiveVectorPoint v hv) :=
        MulAction.mem_orbit _ t
      have hmem := Eq.mp (congrArg (fun S : Set (projectiveVariety ℂ I).points =>
        t • projectiveVectorPoint v hv ∈ S) hOrbit) hmem0
      exact MulAction.mem_fixedPoints'.mp hfixed _ hmem

private theorem flag_moment_transport {I V : Type} [Fintype I] [DecidableEq I]
    (G : ReductiveGroupData ℂ) [AddCommGroup V] [Module ℂ V]
    [Comodule ℂ G.coordinateAlgebra V] (b : Module.Basis I ℂ V)
    (chi : I → G.torusIndex →₀ ℤ)
    (hb : ∀ i, b i ∈ DiagonalizableGroup.weightSpace V G.torusSplit.toCoalgHom
      (ofAdd (chi i))) :
    let : ModObj (reductiveVariety G).toOver (projectiveVariety ℂ I).toOver :=
      @comoduleProjectiveAction ℂ G.coordinateAlgebra I V
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance b
    ∀ (f : (flagVariety G).toOver ⟶ (projectiveVariety ℂ I).toOver)
      (_hEq : IsModHom (reductiveVariety G).toOver f) (_hProper : IsProper f.left)
      (_hInject : Function.Injective (Variety.mapPoints f)),
      let mu := fun x : (flagVariety G).points =>
        momentMap (fun i j => (chi i j : ℝ)) (projectivePointsEquiv.symm (Variety.mapPoints f x))
      let P := fun x : (flagVariety G).points =>
        weightPolytope (fun i j => (chi i j : ℝ))
          (projectivePointsEquiv.symm (Variety.mapPoints f x))
      ∀ x : (flagVariety G).points,
        mu '' MulAction.orbit (torusVariety G).points x = intrinsicInterior ℝ (P x) ∧
        mu '' {y | (flagVariety G).pointMap y ∈
          orbitClosure (torusVariety G) (flagVariety G) x} = P x ∧
        orbitDim (torusVariety G) (flagVariety G) x =
          WithBot.map (fun n : ℕ => (n : ℕ∞)) (affineSpan ℝ (P x)).finDim ∧
        (∀ F : Set (G.torusIndex → ℝ), F.Nonempty → IsExposed ℝ (P x) F →
          ∃ y : (flagVariety G).points,
            (flagVariety G).pointMap y ∈
              orbitClosure (torusVariety G) (flagVariety G) x ∧ P y = F) ∧
        ∀ q : G.torusIndex → ℝ, P x = {q} → ∀ t : (torusVariety G).points, t • x = x := by
  classical
  let : ModObj (reductiveVariety G).toOver (projectiveVariety ℂ I).toOver :=
    @comoduleProjectiveAction ℂ G.coordinateAlgebra I V
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance b
  dsimp only
  intro f hEq hProper hInject x
  have : IsModHom (reductiveVariety G).toOver f := hEq
  have : IsProper f.left := hProper
  let := Mod.scalarRestriction (torusInclusion G) (projectiveVariety ℂ I).toOver
  have hT : IsModHom (torusVariety G).toOver f :=
    @Mod.scalarRestriction_hom (Over (Spec (CommRingCat.of ℂ))) inferInstance inferInstance
      (Over (Spec (CommRingCat.of ℂ))) inferInstance inferInstance
      (torusVariety G).toOver (reductiveVariety G).toOver inferInstance inferInstance
      (torusInclusion G) inferInstance (flagVariety G).toOver (projectiveVariety ℂ I).toOver
      inferInstance inferInstance f hEq
  have : IsModHom (torusVariety G).toOver f := hT
  let mu := fun p : (projectiveVariety ℂ I).points =>
    momentMap (fun i j => (chi i j : ℝ)) (projectivePointsEquiv.symm p)
  let P := fun p : (projectiveVariety ℂ I).points =>
    weightPolytope (fun i j => (chi i j : ℝ)) (projectivePointsEquiv.symm p)
  have hpacket := @torus_projective_moment I V inferInstance inferInstance G
    inferInstance inferInstance inferInstance b chi hb
  obtain ⟨hOrbit, hClosure, hDim, hFaces, hFixed⟩ := hpacket (Variety.mapPoints f x)
  have hOrbitImage := @Variety.mapPoints_orbit ℂ inferInstance (torusVariety G)
    (flagVariety G) (projectiveVariety ℂ I) inferInstance inferInstance inferInstance f hT x
  have hClosureImage := @orbitClosure_points_image ℂ inferInstance (torusVariety G)
    (flagVariety G) (projectiveVariety ℂ I) inferInstance inferInstance inferInstance
    inferInstance f hT hProper x
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (Set.image_image mu (Variety.mapPoints f)
      (MulAction.orbit (torusVariety G).points x)).symm.trans
      ((congrArg (Set.image mu) hOrbitImage).trans hOrbit)
  · exact (Set.image_image mu (Variety.mapPoints f)
      {y | (flagVariety G).pointMap y ∈
        orbitClosure (torusVariety G) (flagVariety G) x}).symm.trans
      ((congrArg (Set.image mu) hClosureImage).trans hClosure)
  · have hd := @orbitDim_of_injective_points ℂ inferInstance (torusVariety G)
      (flagVariety G) (projectiveVariety ℂ I) inferInstance inferInstance inferInstance
      inferInstance inferInstance f hT hInject x
    exact hd.trans hDim
  · intro F hne hF
    obtain ⟨q, hq, hP⟩ := hFaces F hne hF
    have hqImage : q ∈ Variety.mapPoints f ''
        {y | (flagVariety G).pointMap y ∈
          orbitClosure (torusVariety G) (flagVariety G) x} :=
      Eq.mp (congrArg (fun S : Set (projectiveVariety ℂ I).points => q ∈ S)
        hClosureImage.symm) hq
    obtain ⟨y, hy, hfy⟩ := hqImage
    exact ⟨y, hy, (congrArg P hfy).trans hP⟩
  · intro q hq t
    apply hInject
    exact (@Variety.mapPoints_smul ℂ inferInstance (torusVariety G)
      (flagVariety G) (projectiveVariety ℂ I) inferInstance inferInstance inferInstance
      f hT t x).trans (hFixed q hq t)

private theorem reindex_mem {K I V : Type} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis I K V) (P : Submodule K V) (i : ULift I) (hi : b i.down ∈ P) :
    b.reindex Equiv.ulift.symm i ∈ P := by
  rw [Module.Basis.reindex_apply]
  exact hi

/-- The adjoint exterior coordinates define a moment map on flag rational points. -/
def flagMomentMap (G : ReductiveGroupData ℂ) :
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
    (w : ⋀[ℂ]^d G.tangent) → (hw : w ≠ 0) →
      (∀ g ∈ G.borelPoints, reductivePointsMulEquiv G g •
        comoduleProjectivePoint b w hw = comoduleProjectivePoint b w hw) →
      (flagVariety G).points → (G.torusIndex → ℝ) :=
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
  fun w hw hB x =>
    momentMap (fun (s : ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)) j =>
      ((toAdd (∏ i ∈ s.down.val, adjointWeightCharacter G.torusSplit i)) j : ℝ))
      (projectivePointsEquiv.symm (Variety.mapPoints
        (flagOrbitMorphism G (projectiveVariety ℂ
          (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
          (comoduleProjectivePoint b w hw) hB) x))

/-- One adjoint exterior line gives the torus moment and face formulas for every flag. -/
theorem exists_flag_moment_map (G : ReductiveGroupData ℂ) :
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
      IsModHom (reductiveVariety G).toOver f ∧
      Function.Injective (Variety.mapPoints f) ∧
      let chi := fun s : ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d) =>
        toAdd (∏ i ∈ s.down.val, adjointWeightCharacter G.torusSplit i)
      let P := fun x : (flagVariety G).points =>
        weightPolytope (fun i j => (chi i j : ℝ))
          (projectivePointsEquiv.symm (Variety.mapPoints f x))
      ∀ x : (flagVariety G).points,
        flagMomentMap G w hw hB '' MulAction.orbit (torusVariety G).points x =
          intrinsicInterior ℝ (P x) ∧
        flagMomentMap G w hw hB '' {y | (flagVariety G).pointMap y ∈
          orbitClosure (torusVariety G) (flagVariety G) x} = P x ∧
        orbitDim (torusVariety G) (flagVariety G) x =
          WithBot.map (fun n : ℕ => (n : ℕ∞)) (affineSpan ℝ (P x)).finDim ∧
        (∀ F : Set (G.torusIndex → ℝ), F.Nonempty → IsExposed ℝ (P x) F →
          ∃ y : (flagVariety G).points,
            (flagVariety G).pointMap y ∈
              orbitClosure (torusVariety G) (flagVariety G) x ∧ P y = F) ∧
        ∀ q : G.torusIndex → ℝ, P x = {q} → ∀ t : (torusVariety G).points, t • x = x := by
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
  have hEmbedding := @exists_adjoint_flag_embedding ℂ inferInstance inferInstance inferInstance G
  obtain ⟨w, hw, hB, hdet, hEq, hProper, hInject, _⟩ := hEmbedding
  let f := flagOrbitMorphism G (projectiveVariety ℂ
    (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
    (comoduleProjectivePoint b w hw) hB
  let chi := fun s : ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d) =>
    toAdd (∏ i ∈ s.down.val, adjointWeightCharacter G.torusSplit i)
  have hb : ∀ i, b i ∈ DiagonalizableGroup.weightSpace (⋀[ℂ]^d G.tangent)
      G.torusSplit.toCoalgHom (ofAdd (chi i)) := by
    intro i
    have hi := @exteriorBasis_weightSpace ℂ G.coordinateAlgebra G.tangent G.characters
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (adjointWeightRank G.torusSplit) G.torusSplit
      (adjointWeightBasis G.torusSplit) (adjointWeightCharacter G.torusSplit)
      (@adjointWeightBasis_weightSpace ℂ G.coordinateAlgebra G.characters
        inferInstance inferInstance inferInstance inferInstance inferInstance G.torusSplit)
      d i.down
    simp only [chi, ofAdd_toAdd]
    exact @reindex_mem ℂ (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)
      (⋀[ℂ]^d G.tangent) inferInstance inferInstance inferInstance
      ((adjointWeightBasis G.torusSplit).exteriorPower d)
      (DiagonalizableGroup.weightSpace (⋀[ℂ]^d G.tangent) G.torusSplit.toCoalgHom
        (∏ j ∈ i.down.val, adjointWeightCharacter G.torusSplit j)) i hi
  refine ⟨w, hw, hB, hdet, hEq, hInject, ?_⟩
  have hMoment := @flag_moment_transport
    (ULift.{0} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)) (⋀[ℂ]^d G.tangent)
    inferInstance inferInstance G inferInstance inferInstance inferInstance b chi hb
    f hEq hProper hInject
  simpa only [flagMomentMap] using hMoment

end SchubertGeometry
