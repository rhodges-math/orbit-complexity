import OrbitComplexity.Paper.Heart.Complement

/-!
# Orbit dynamics in a Schubert cell

Unique parabolic and heart factors control which unipotent products stay in the
heart, and move every Schubert-cell flag into the heart.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem parabolic_le_inversions (I : Set G.rootBase.support) (w : G.weylGroup) :
    G.rootSubsetPoints
      (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) ≤
    G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) := by
  apply G.rootSubsetPoints_mono
  intro r hr
  rw [inversionRoots_eq_union_heart G I w]
  exact Or.inl hr

/-- A parabolic inversion factor preserves membership in Vd exactly when it is the identity. -/
theorem parabolic_mul_vd_mem_iff (I : Set G.rootBase.support) (w : G.weylGroup)
    (u v : G.points)
    (hu : u ∈ G.rootSubsetPoints
      (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _))
    (hv : v ∈ Vd.points G I w) : u * v ∈ Vd.points G I w ↔ u = 1 := by
  have huv := (G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)).mul_mem
      (parabolic_le_inversions G I w hu) (Vd.points_le_inversions G I w hv)
  obtain ⟨p, hp, huniq⟩ := Vd.existsUnique_mul G I w (u * v) huv
  constructor
  · intro h
    have he : (u, v) = (1, u * v) :=
      (huniq (u, v) ⟨hu, hv, rfl⟩).trans
        (huniq (1, u * v) ⟨Subgroup.one_mem _, h, one_mul _⟩).symm
    exact congrArg Prod.fst he
  · rintro rfl
    simpa only [one_mul] using hv

/-- A nonidentity parabolic inversion point moves every heart flag outside the heart. -/
theorem parabolic_smul_not_mem_heart (I : Set G.rootBase.support) (w : G.weylGroup)
    (u : G.points)
    (hu : u ∈ G.rootSubsetPoints
      (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _))
    (hne : u ≠ 1) (q : (flagVariety G).points)
    (hq : q ∈ Set.range (Variety.mapPoints (heartInclusion G I w))) :
    reductivePointsMulEquiv G u • q ∉
      Set.range (Variety.mapPoints (heartInclusion G I w)) := by
  obtain ⟨v, hv, rfl⟩ := (mem_heart_iff G I w q).mp hq
  intro h
  obtain ⟨z, hz, he⟩ := (mem_heart_iff G I w _).mp h
  have huv := (G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)).mul_mem
      (parabolic_le_inversions G I w hu) (Vd.points_le_inversions G I w hv)
  have hact : reductivePointsMulEquiv G u •
      flagVarietyPointsEquiv G (flagProjection G (v * G.weylPoint w)) =
        flagVarietyPointsEquiv G (flagProjection G ((u * v) * G.weylPoint w)) := by
    rw [flagVarietyAction_points, ← flagProjection_smul, mul_assoc]
  have hp : schubertPointMap G w ⟨u * v, huv⟩ =
      schubertPointMap G w ⟨z, Vd.points_le_inversions G I w hz⟩ := by
    exact (flagVarietyPointsEquiv G).injective (hact.symm.trans he.symm)
  have heuv : u * v = z := congrArg Subtype.val (schubertPointMap_injective G w hp)
  exact hne ((parabolic_mul_vd_mem_iff G I w u v hu hv).mp (heuv.symm ▸ hz))

private theorem torus_raw_heart_stable (I : Set G.rootBase.support) (w : G.weylGroup)
    (t : G.points) (ht : t ∈ G.torusPoints) (q : (flagVariety G).points)
    (hq : q ∈ Set.range (Variety.mapPoints (heartInclusion G I w))) :
    reductivePointsMulEquiv G t • q ∈
      Set.range (Variety.mapPoints (heartInclusion G I w)) := by
  let s := (torusPointsMulEquiv G).symm ⟨t, ht⟩
  have h := heart_torus_stable G I w s hq
  rw [Variety.restricted_smul (torusInclusion G), torusInclusion_points,
    show torusPointsMulEquiv G s = ⟨t, ht⟩ from MulEquiv.apply_symm_apply _ _] at h
  exact h

/-- Torus and complementary unipotent multiplication preserve the complement of the heart. -/
theorem torus_complement_not_mem_heart (I : Set G.rootBase.support) (w : G.weylGroup)
    (t u : G.points) (ht : t ∈ G.torusPoints)
    (hu : u ∈ G.rootSubsetPoints (complementRootIndices G I w)
      (complementRootIndices_closed G I w))
    (q : (flagVariety G).points)
    (hq : q ∉ Set.range (Variety.mapPoints (heartInclusion G I w))) :
    reductivePointsMulEquiv G (t * u) • q ∉
      Set.range (Variety.mapPoints (heartInclusion G I w)) := by
  intro h
  have htinv := torus_raw_heart_stable G I w t⁻¹ (G.torusPoints.inv_mem ht) _ h
  have huinv := complement_heart_stable G I w u⁻¹
    ((G.rootSubsetPoints _ _).inv_mem hu) _ htinv
  apply hq
  simpa only [map_mul, map_inv, mul_smul, inv_smul_smul] using huinv

/-- A Levi--Borel factor carrying a heart point to a heart point has trivial Ua factor. -/
theorem heart_factor_eq_one (I : Set G.rootBase.support) (w : G.weylGroup)
    (t u₁ u₂ : G.points) (ht : t ∈ G.torusPoints)
    (hu₁ : u₁ ∈ G.rootSubsetPoints (complementRootIndices G I w)
      (complementRootIndices_closed G I w))
    (hu₂ : u₂ ∈ G.rootSubsetPoints
      (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _))
    (h₁ h₂ : (flagVariety G).points)
    (hh₁ : h₁ ∈ Set.range (Variety.mapPoints (heartInclusion G I w)))
    (hh₂ : h₂ ∈ Set.range (Variety.mapPoints (heartInclusion G I w)))
    (he : reductivePointsMulEquiv G (t * u₁ * u₂) • h₁ = h₂) :
    u₂ = 1 ∧ reductivePointsMulEquiv G (t * u₁) • h₁ = h₂ := by
  have hu₂one : u₂ = 1 := by
    by_contra hne
    have hnot := torus_complement_not_mem_heart G I w t u₁ ht hu₁ _
      (parabolic_smul_not_mem_heart G I w u₂ hu₂ hne h₁ hh₁)
    apply hnot
    rw [← he] at hh₂
    simpa only [map_mul, mul_smul] using hh₂
  refine ⟨hu₂one, ?_⟩
  simpa only [hu₂one, mul_one] using he

/-- Every Schubert-cell flag can be moved into the heart by a parabolic inversion point. -/
theorem exists_parabolic_smul_heart (I : Set G.rootBase.support) (w : G.weylGroup)
    (q : (flagVariety G).points)
    (hq : q ∈ Set.range (Variety.mapPoints (schubertCellInclusion G w))) :
    ∃ u ∈ G.rootSubsetPoints
      (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _),
      reductivePointsMulEquiv G u • q ∈
        Set.range (Variety.mapPoints (heartInclusion G I w)) := by
  rw [← schubertRootMorphism_range] at hq
  obtain ⟨x, rfl⟩ := hq
  let z : G.points := rootSubsetPointsMulEquiv G _
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) x
  have hz : z ∈ G.rootSubsetPoints (leftRootInversionIndices G.rootBase w)
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) :=
    (rootSubsetPointsMulEquiv G _ _ x).property
  obtain ⟨p, ⟨hp₁, hp₂, hprod⟩, _⟩ := Vd.existsUnique_mul G I w z hz
  refine ⟨p.1⁻¹, (G.rootSubsetPoints _ _).inv_mem hp₁, ?_⟩
  apply (mem_heart_iff G I w _).mpr
  refine ⟨p.2, hp₂, ?_⟩
  rw [schubertRootMorphism_points, flagVarietyAction_points, ← flagProjection_smul]
  apply congrArg (flagVarietyPointsEquiv G)
  apply congrArg (flagProjection G)
  change p.2 * G.weylPoint w = p.1⁻¹ * (z * G.weylPoint w)
  rw [← hprod]
  group

end SchubertOrbits
