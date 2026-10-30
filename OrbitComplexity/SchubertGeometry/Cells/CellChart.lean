import OrbitComplexity.SchubertGeometry.Cells.ConjugatedRoot

/-! # Affine charts on Schubert cells

The Weyl-translated opposite chart realizes the inversion-root subgroup as its Schubert cell.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The root-cell morphism is its closed root embedding followed by the opposite flag chart. -/
theorem schubertRootMorphism_chart (w : G.weylGroup) :
    schubertOppositeMorphism G w ≫ flagChartMorphism G (G.weylPoint w) =
      schubertRootMorphism G w := by
  apply GroupActions.Variety.mapPoints_injective
  funext x
  have hc : flagChartPoint G (G.weylPoint w)
      (GroupActions.Variety.mapPoints (schubertOppositeMorphism G w) x) =
      flagProjection G ((schubertUnipotentPointsEquiv G w x : G.points) * G.weylPoint w) := by
    change flagProjection G (G.weylPoint w *
      (GroupActions.oppositeUnipotentPointsMulEquiv G
        (GroupActions.Variety.mapPoints (schubertOppositeMorphism G w) x) : G.points)) = _
    rw [schubertOppositeMorphism_points]
    congr 1
    group
  exact (GroupActions.Variety.mapPoints_comp (schubertOppositeMorphism G w)
    (flagChartMorphism G (G.weylPoint w)) x).trans
      ((flagChartMorphism_points G (G.weylPoint w) _).trans
        ((congrArg (flagVarietyPointsEquiv G) hc).trans
          (schubertRootMorphism_points G w x).symm))

/-- The inversion-root morphism is a locally closed embedding into the flag variety. -/
instance schubertRoot_isPreimmersion (w : G.weylGroup) :
    IsPreimmersion (schubertRootMorphism G w).left := by
  rw [← schubertRootMorphism_chart]
  change IsPreimmersion ((schubertOppositeMorphism G w).left ≫
    (flagChartMorphism G (G.weylPoint w)).left)
  infer_instance

/-- Inversion-root coordinates identify their affine subgroup with the Schubert cell. -/
def schubertCellIso (w : G.weylGroup) :
    (schubertUnipotent G w).toOver ≅ (schubertCell G w).toOver :=
  GroupActions.Variety.pointImageIso (schubertRootMorphism G w) (schubertCellInclusion G w)
    (schubertRootMorphism_range G w)

/-- The affine-cell isomorphism commutes with the two maps to the flag variety. -/
theorem schubertCellIso_hom_comp (w : G.weylGroup) :
    (schubertCellIso G w).hom ≫ schubertCellInclusion G w = schubertRootMorphism G w :=
  GroupActions.Variety.pointImageIso_hom_comp _ _ (schubertRootMorphism_range G w)

/-- A Schubert cell has dimension its Weyl inversion count. -/
theorem schubertCell_dim (w : G.weylGroup) :
    (schubertCell G w).dim = ReductiveGroups.rootInversionCount G.rootBase w :=
  (GroupActions.Variety.dim_eq_of_iso _ (schubertCellIso G w)).symm.trans
    (schubertUnipotent_dim G w)

/-- A Schubert cell is affine space with one coordinate for each Weyl inversion. -/
def schubertCellChart (w : G.weylGroup) :
    (GroupActions.affineVariety K
      (MvPolynomial (Fin (ReductiveGroups.rootInversionCount G.rootBase w)) K)).toOver ≅
        (schubertCell G w).toOver := by
  let I := {r : G.rootIndex // G.rootBase.IsPos r ∧
    r ∈ ReductiveGroups.leftRootInversionIndices G.rootBase w}
  have hc : Nat.card I = ReductiveGroups.rootInversionCount G.rootBase w := by
    have hd : (Nat.card I : WithBot ℕ∞) =
        ReductiveGroups.rootInversionCount G.rootBase w :=
      (GroupActions.rootSubsetVariety_dim G _
        (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)).symm.trans
          (schubertUnipotent_dim G w)
    exact_mod_cast hd
  let e : I ≃ Fin (ReductiveGroups.rootInversionCount G.rootBase w) :=
    (Finite.equivFin I).trans (finCongr hc)
  exact (algSpec (CommRingCat.of K)).mapIso (CommAlgCat.isoMk
    (MvPolynomial.renameEquiv K e)).op ≪≫ schubertUnipotentChart G w ≪≫ schubertCellIso G w

/-- A Schubert variety has the dimension of its dense Schubert cell. -/
theorem schubertVariety_dim (w : G.weylGroup) :
    (schubertVariety G w).dim = ReductiveGroups.rootInversionCount G.rootBase w := by
  let e : (schubertVariety G w).scheme ≃ₜ
      closure (Set.range (schubertCellInclusion G w).left) :=
    (schubertInclusion G w).left.isEmbedding.toHomeomorph.trans
      (.setCongr (schubertInclusion_range G w))
  have hd : (schubertCell G w).dim =
      topologicalKrullDim (closure (Set.range (schubertCellInclusion G w).left)) := by
    rw [GroupActions.orbitInclusion_range, ← GroupActions.orbitClosure_eq]
    exact GroupActions.orbitVariety_dim _ _ _
  exact e.isHomeomorph.topologicalKrullDim_eq.trans (hd.symm.trans (schubertCell_dim G w))

end
end SchubertGeometry
