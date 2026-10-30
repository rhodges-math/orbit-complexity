import OrbitComplexity.SchubertGeometry.FlagVariety.OrbitMorphism
import OrbitComplexity.SchubertGeometry.Cells.Bruhat
import OrbitComplexity.GroupActions.Representations.ProjectiveAction
import OrbitComplexity.GroupActions.Representations.ExteriorLine
import OrbitComplexity.GroupActions.Representations.ExteriorActions
import OrbitComplexity.ReductiveGroups.Groups.Characters.CharacterWeightDecomposition
import Batteries.Tactic.Lint

/-! # The adjoint exterior orbit of the flag variety

The top exterior line of the Borel tangent has Borel stabilizer. Its orbit morphism
therefore gives a proper equivariant map of flags with injective rational-point map.
-/

open CategoryTheory AlgebraicGeometry TauCeti ReductiveGroups GroupActions
noncomputable section
namespace SchubertGeometry
universe u v

private theorem exterior_projective_fixed_iff
    {K H ι : Type u} {V : Type v} [Field K] [CharZero K]
    [CommRing H] [HopfAlgebra K H] [IsReduced H] [Algebra.FiniteType K H]
    [IsAlgClosed K] [AddCommGroup V] [Module K V] [Comodule K H V]
    [Fintype ι] [DecidableEq ι] (d : ℕ) (b : Module.Basis ι K (⋀[K]^d V))
    (w : ⋀[K]^d V) (hw : w ≠ 0) (e : V ≃ₗ[K] V)
    (g : WithConv (H →ₐ[K] K))
    (hg : Comodule.basePointsRepresentation (H := H) V g = e.toLinearMap) :
    let := exteriorPowerComodule (K := K) (H := H) (V := V) d
    let := comoduleProjectiveAction (H := H) b
    affineGroupPointsMulEquiv K H g • comoduleProjectivePoint b w hw =
        comoduleProjectivePoint b w hw ↔
      (Submodule.span K {w}).map (exteriorPower.map d e.toLinearMap) =
        Submodule.span K {w} := by
  let := exteriorPowerComodule (K := K) (H := H) (V := V) d
  let := comoduleProjectiveAction (H := H) b
  dsimp only
  rw [comoduleProjective_stabilizer, exteriorPower_basePoints,
    Representation.exteriorPower_apply, hg]


section Adjoint
variable {K ι : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
  (G : ReductiveGroupData K) [iFin : Fintype ι] [iDecEq : DecidableEq ι]

private theorem adjoint_projective_fixed_iff
    (b : Module.Basis ι K (⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent))
    (w : ⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent) (hw : w ≠ 0)
    (hline : ∀ e : G.tangent ≃ₗ[K] G.tangent,
      (Submodule.span K {w}).map
          (exteriorPower.map (Module.finrank K G.borelTangent.toSubmodule) e.toLinearMap) =
        Submodule.span K {w} ↔ G.borelTangent.toSubmodule.map e.toLinearMap =
          G.borelTangent.toSubmodule) (g : G.points) :
    let := affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)
    let := exteriorPowerComodule (K := K) (H := G.coordinateAlgebra) (V := G.tangent)
      (Module.finrank K G.borelTangent.toSubmodule)
    let : ModObj (reductiveVariety G).toOver (projectiveVariety K ι).toOver :=
      @comoduleProjectiveAction K G.coordinateAlgebra ι
        (⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent)
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance b
    reductivePointsMulEquiv G g • comoduleProjectivePoint b w hw =
        comoduleProjectivePoint b w hw ↔ g ∈ G.borelPoints := by
  let := affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)
  let := exteriorPowerComodule (K := K) (H := G.coordinateAlgebra) (V := G.tangent)
    (Module.finrank K G.borelTangent.toSubmodule)
  let : ModObj (reductiveVariety G).toOver (projectiveVariety K ι).toOver :=
      @comoduleProjectiveAction K G.coordinateAlgebra ι
        (⋀[K]^(Module.finrank K G.borelTangent.toSubmodule) G.tangent)
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance b
  dsimp only
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv
    (Representation.asGroupHom
      (affineGroupAdjointRepresentation (K := K) (B := G.coordinateAlgebra)) g)
  have hg : Comodule.basePointsRepresentation (H := G.coordinateAlgebra) G.tangent g =
      e.toLinearMap := affineGroupAdjointComodule_points g
  have hi := exterior_projective_fixed_iff
    (Module.finrank K G.borelTangent.toSubmodule) b w hw e g hg
  have hp : reductivePointsMulEquiv G g =
      affineGroupPointsMulEquiv K G.coordinateAlgebra g := rfl
  rw [hp]
  exact hi.trans ((hline e).trans (borelTangent_map_eq_iff G g))

end Adjoint

section Embedding
variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
  (G : ReductiveGroupData K)

/-- The Borel top exterior line gives a proper equivariant map with injective rational points.
The vector is chosen once, and its determinant formula is retained. -/
theorem exists_adjoint_flag_embedding :
    let d := Module.finrank K G.borelTangent.toSubmodule
    let b := ((adjointWeightBasis G.torusSplit).exteriorPower d).reindex Equiv.ulift.symm
    let := affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)
    let := exteriorPowerComodule (K := K) (H := G.coordinateAlgebra) (V := G.tangent) d
    let : ModObj (reductiveVariety G).toOver
        (projectiveVariety K
          (ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))).toOver :=
      @comoduleProjectiveAction K G.coordinateAlgebra
        (ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)) (⋀[K]^d G.tangent)
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance b
    ∃ (w : ⋀[K]^d G.tangent) (hw : w ≠ 0)
      (hB : ∀ g ∈ G.borelPoints, reductivePointsMulEquiv G g •
        comoduleProjectivePoint b w hw = comoduleProjectivePoint b w hw),
      (∀ (e : G.tangent ≃ₗ[K] G.tangent)
        (hF : G.borelTangent.toSubmodule.map e.toLinearMap = G.borelTangent.toSubmodule),
        exteriorPower.map d e.toLinearMap w =
          LinearMap.det (e.ofSubmodules G.borelTangent.toSubmodule
            G.borelTangent.toSubmodule hF).toLinearMap • w) ∧
      IsModHom (reductiveVariety G).toOver
        (flagOrbitMorphism G (projectiveVariety K
          (ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
          (comoduleProjectivePoint b w hw) hB) ∧
      IsProper (flagOrbitMorphism G (projectiveVariety K
          (ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
          (comoduleProjectivePoint b w hw) hB).left ∧
      Function.Injective (Variety.mapPoints
        (flagOrbitMorphism G (projectiveVariety K
          (ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
          (comoduleProjectivePoint b w hw) hB)) ∧
      ∀ g : G.points,
        reductivePointsMulEquiv G g • comoduleProjectivePoint b w hw =
          comoduleProjectivePoint b w hw ↔ g ∈ G.borelPoints := by
  classical
  let d := Module.finrank K G.borelTangent.toSubmodule
  let b := ((adjointWeightBasis G.torusSplit).exteriorPower d).reindex Equiv.ulift.symm
  let := affineGroupAdjointComodule (K := K) (B := G.coordinateAlgebra)
  let := exteriorPowerComodule (K := K) (H := G.coordinateAlgebra) (V := G.tangent) d
  let : ModObj (reductiveVariety G).toOver
        (projectiveVariety K
          (ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))).toOver :=
      @comoduleProjectiveAction K G.coordinateAlgebra
        (ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)) (⋀[K]^d G.tangent)
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance b
  obtain ⟨w, hw, hdet, hline⟩ := exists_exterior_line_stabilizer G.borelTangent.toSubmodule
  have hfix := @adjoint_projective_fixed_iff K
    (ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d))
    kField kClosed kZero G inferInstance inferInstance b w hw hline
  have hB : ∀ g ∈ G.borelPoints, reductivePointsMulEquiv G g •
      comoduleProjectivePoint b w hw = comoduleProjectivePoint b w hw :=
    fun g hg ↦ (hfix g).mpr hg
  refine ⟨w, hw, hB, hdet, ?_, ?_, ?_, hfix⟩
  · exact @flagOrbitMorphism_isModHom K kField kClosed kZero G
      (projectiveVariety K
        (ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
      inferInstance (comoduleProjectivePoint b w hw) hB
  · exact @flagOrbitMorphism_isProper K kField kClosed kZero G
      (projectiveVariety K
        (ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
      inferInstance (comoduleProjectivePoint b w hw) hB
  · exact @flagOrbitMorphism_injective K kField kClosed kZero G
      (projectiveVariety K
        (ULift.{u} (Set.powersetCard (Fin (adjointWeightRank G.torusSplit)) d)))
      inferInstance (comoduleProjectivePoint b w hw) hB (fun g hg ↦ (hfix g).mp hg)

end Embedding

end SchubertGeometry
