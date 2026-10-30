import OrbitComplexity.Paper.Heart.Isomorphism
import OrbitComplexity.ReductiveGroups.Roots.Parabolic.LeviRootClosed

/-!
# The complementary unipotent action on the heart

Conjugating complementary parabolic roots by the inverse parabolic factor gives
positive roots. Borel stability of the minimal cell therefore preserves the heart.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The parabolic positive roots outside the inversions of the parabolic factor. -/
def complementRootIndices (I : Set G.rootBase.support) (w : G.weylGroup) :
    Set G.rootIndex :=
  leviPositiveRoots G.rootBase I ∩
    {r | G.rootBase.IsPos r ∧
      r ∉ leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w)}

/-- The parabolic complement is an integrally closed positive-root support. -/
theorem complementRootIndices_closed (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsPositiveRootClosed G.rootBase (complementRootIndices G I w) :=
  (LeviRootSpan.isPositiveRootClosed G.rootBase I).inter
    (PositiveRootClosedSets.isPositiveRootClosed G.rootBase _)

private theorem heart_mem_iff_inverse_translate (I : Set G.rootBase.support)
    (w : G.weylGroup) (q : (flagVariety G).points) :
    q ∈ Set.range (Variety.mapPoints (heartInclusion G I w)) ↔
      (reductivePointsMulEquiv G (G.weylPoint (leftParabolicFactor G.rootBase I w)))⁻¹ • q ∈
        Set.range (Variety.mapPoints (schubertCellInclusion G
          (leftParabolicRepresentative G.rootBase I w))) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Variety.mapPoints (heartMinimalIso G I w).hom x,
      heartMinimalIso_points G I w x⟩
  · rintro ⟨y, hy⟩
    let x := (Variety.pointsHomeomorph (heartMinimalIso G I w)).symm y
    have hx : Variety.mapPoints (heartMinimalIso G I w).hom x = y :=
      (Variety.pointsHomeomorph (heartMinimalIso G I w)).apply_symm_apply y
    refine ⟨x, ?_⟩
    apply MulAction.injective
      (reductivePointsMulEquiv G (G.weylPoint (leftParabolicFactor G.rootBase I w)))⁻¹
    have h := heartMinimalIso_points G I w x
    rw [hx] at h
    exact h.symm.trans hy

/-- The parabolic-complement unipotent group preserves the heart under left multiplication. -/
theorem complement_heart_stable (I : Set G.rootBase.support) (w : G.weylGroup)
    (u : G.points)
    (hu : u ∈ G.rootSubsetPoints (complementRootIndices G I w)
      (complementRootIndices_closed G I w))
    (q : (flagVariety G).points)
    (hq : q ∈ Set.range (Variety.mapPoints (heartInclusion G I w))) :
    reductivePointsMulEquiv G u • q ∈
      Set.range (Variety.mapPoints (heartInclusion G I w)) := by
  let a := leftParabolicFactor G.rootBase I w
  have hpos : u ∈ G.rootSubsetPoints
      {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase a}
      (PositiveRootClosedSets.isPositiveRootClosed G.rootBase a) :=
    G.rootSubsetPoints_mono _ _ _ _ (fun _ hr => hr.2) hu
  have hb : (G.weylPoint a)⁻¹ * u * G.weylPoint a ∈ G.borelPoints :=
    G.unipotent_le_borel (G.noninversionPoints_conj_unipotent a u hpos)
  let b : (borelVariety G).points := (borelPointsMulEquiv G).symm ⟨_, hb⟩
  have hcell := schubertCell_stable G (leftParabolicRepresentative G.rootBase I w) b
    ((heart_mem_iff_inverse_translate G I w q).mp hq)
  apply (heart_mem_iff_inverse_translate G I w _).mpr
  have hs : b •
      ((reductivePointsMulEquiv G (G.weylPoint a))⁻¹ • q) =
      (reductivePointsMulEquiv G (G.weylPoint a))⁻¹ •
        (reductivePointsMulEquiv G u • q) := by
    rw [Variety.restricted_smul (borelInclusion G), borelInclusion_points,
      MulEquiv.apply_symm_apply]
    change reductivePointsMulEquiv G ((G.weylPoint a)⁻¹ * u * G.weylPoint a) • _ = _
    rw [map_mul, map_mul, map_inv]
    simp only [mul_smul, smul_inv_smul]
  exact hs ▸ hcell

/-- The unipotent subgroup of the parabolic positive roots outside the factor inversions. -/
abbrev complementUnipotent (I : Set G.rootBase.support) (w : G.weylGroup) : Variety K :=
  rootSubsetVariety G (complementRootIndices G I w) (complementRootIndices_closed G I w)

private theorem complementFlagStable (I : Set G.rootBase.support) (w : G.weylGroup)
    (u : (complementUnipotent G I w).points) (x : (heart G I w).points) :
    u • Variety.mapPoints (heartInclusion G I w) x ∈
      Set.range (Variety.mapPoints (heartInclusion G I w)) := by
  rw [Variety.restricted_smul (rootSubsetInclusion G _ _), rootSubsetInclusion_points]
  exact complement_heart_stable G I w _
    (rootSubsetPointsMulEquiv G _ (complementRootIndices_closed G I w) u).property _ ⟨x, rfl⟩

/-- The complementary unipotent subgroup acts algebraically on the heart by left multiplication. -/
instance complementHeartAction (I : Set G.rootBase.support) (w : G.weylGroup) :
    ModObj (complementUnipotent G I w).toOver (heart G I w).toOver :=
  Variety.modObjOfInvariant (complementUnipotent G I w) (flagVariety G) (heart G I w)
    (heartInclusion G I w) (complementFlagStable G I w)

/-- The heart inclusion is equivariant for the complementary unipotent group action. -/
instance heartInclusion_complement (I : Set G.rootBase.support) (w : G.weylGroup) :
    IsModHom (complementUnipotent G I w).toOver (heartInclusion G I w) :=
  Variety.modObjOfInvariant_isModHom _ _ _ _ (complementFlagStable G I w)

/-- Complementary unipotent multiplication on the heart agrees with flag multiplication. -/
theorem complement_heart_smul (I : Set G.rootBase.support) (w : G.weylGroup)
    (u : (complementUnipotent G I w).points) (x : (heart G I w).points) :
    Variety.mapPoints (heartInclusion G I w) (u • x) =
      u • Variety.mapPoints (heartInclusion G I w) x :=
  Variety.modObjOfInvariant_smul _ _ _ _ (complementFlagStable G I w) u x

end SchubertOrbits
