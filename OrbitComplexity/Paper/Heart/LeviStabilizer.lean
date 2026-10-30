import OrbitComplexity.SchubertGeometry.Levi.Maps
import OrbitComplexity.Paper.Heart.LeviOrbits
import OrbitComplexity.GroupActions.Actions.Stabilizers
import OrbitComplexity.GroupActions.Varieties.PointImageIso

/-! # Stabilizers at heart points

When the prescribed simple roots are left descents, the Levi--Borel stabilizer of
a heart point has the same closed image as its torus stabilizer.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem torusLevi_smul (I : Set G.rootBase.support)
    (t : (torusVariety G).points) (q : (flagVariety G).points) :
    Variety.mapPoints (torusLeviBorelInclusion G I) t • q = t • q := by
  obtain ⟨f, rfl⟩ := (flagVarietyPointsEquiv G).surjective q
  rw [leviBorelFlag_smul, torusFlag_smul, flagVarietyAction_points,
    torusLeviBorelInclusion_points]

private theorem heartCell_torus (I : Set G.rootBase.support) (w : G.weylGroup)
    (t : (torusVariety G).points) (h : (heart G I w).points) :
    Variety.mapPoints (heartCellInclusion G I w) (t • h) =
      Variety.mapPoints (torusLeviBorelInclusion G I) t •
        Variety.mapPoints (heartCellInclusion G I w) h := by
  apply Variety.mapPoints_injective_of_mono (schubertCellInclusion G w)
  rw [← Variety.mapPoints_comp, heartCellInclusion_comp, leviBorelCell_smul,
    ← Variety.mapPoints_comp, heartCellInclusion_comp, torusLevi_smul]
  exact heart_torus_smul G I w t h

private theorem heartLevi_stabilizer (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
    (h : (heart G I w).points) (b : (leviBorelVariety G I).points)
    (hb : b • Variety.mapPoints (heartCellInclusion G I w) h =
      Variety.mapPoints (heartCellInclusion G I w) h) :
    ∃ t : (torusVariety G).points, t • h = h ∧
      Variety.mapPoints (torusLeviBorelInclusion G I) t = b := by
  obtain ⟨t, ht, u, hu, htu⟩ := G.leviBorel_exists_torus_mul I
    (leviBorelPointsMulEquiv G I b) (leviBorelPointsMulEquiv G I b).property
  have ha := (leftFactor_longest_iff G.rootBase I w).2.mpr hI
  have hroot : leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) =
      leviPositiveRoots G.rootBase I := by rw [ha, leftRootInv_longestParabolic]
  have hu' : u ∈ G.rootSubsetPoints
      (leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w))
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _) := by
    simpa only [hroot] using hu
  have he := congrArg (Variety.mapPoints (schubertCellInclusion G w)) hb
  rw [leviBorelCell_smul, ← Variety.mapPoints_comp, heartCellInclusion_comp,
    leviBorelFlag_smul] at he
  have he' : reductivePointsMulEquiv G (t * 1 * u) •
      Variety.mapPoints (heartInclusion G I w) h =
        Variety.mapPoints (heartInclusion G I w) h := by
    simpa only [mul_one, htu] using he
  obtain ⟨hu1, _⟩ := heart_factor_eq_one G I w t 1 u ht (Subgroup.one_mem _) hu'
    _ _ ⟨h, rfl⟩ ⟨h, rfl⟩ he'
  have htb : t = (leviBorelPointsMulEquiv G I b : G.points) := by
    simpa only [hu1, mul_one] using htu
  let tp := (torusPointsMulEquiv G).symm ⟨t, ht⟩
  have htp : Variety.mapPoints (torusLeviBorelInclusion G I) tp = b := by
    apply (leviBorelPointsMulEquiv G I).injective
    apply Subtype.ext
    rw [torusLeviBorelInclusion_points]
    exact (congrArg Subtype.val ((torusPointsMulEquiv G).apply_symm_apply ⟨t, ht⟩)).trans htb
  refine ⟨tp, ?_, htp⟩
  apply Variety.mapPoints_injective_of_mono (heartCellInclusion G I w)
  rw [heartCell_torus, htp]
  exact hb

/-- Torus and Levi--Borel stabilizers at a heart point have equal closed images. -/
theorem heartStabilizer_range (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
    (h : (heart G I w).points) :
    Set.range (Variety.mapPoints
      (stabilizerInclusion (torusVariety G) (heart G I w) h ≫ torusLeviBorelInclusion G I)) =
      Set.range (Variety.mapPoints (stabilizerInclusion (leviBorelVariety G I)
        (schubertCell G w) (Variety.mapPoints (heartCellInclusion G I w) h))) := by
  ext b
  constructor
  · rintro ⟨s, rfl⟩
    let t := stabilizerPointsEquiv (torusVariety G) (heart G I w) h s
    have ht : t.val • h = h := MulAction.mem_stabilizer_iff.mp t.property
    have hs : Variety.mapPoints (stabilizerInclusion (torusVariety G) (heart G I w) h) s =
        t.val := rfl
    let b' := Variety.mapPoints (torusLeviBorelInclusion G I) t.val
    have hb' : b' • Variety.mapPoints (heartCellInclusion G I w) h =
        Variety.mapPoints (heartCellInclusion G I w) h :=
      (heartCell_torus G I w t.val h).symm.trans
        (congrArg (Variety.mapPoints (heartCellInclusion G I w)) ht)
    let sp := (stabilizerPointsEquiv (leviBorelVariety G I) (schubertCell G w)
      (Variety.mapPoints (heartCellInclusion G I w) h)).symm
        ⟨b', MulAction.mem_stabilizer_iff.mpr hb'⟩
    refine ⟨sp, ?_⟩
    rw [Variety.mapPoints_comp, hs]
    exact congrArg Subtype.val ((stabilizerPointsEquiv (leviBorelVariety G I)
      (schubertCell G w) (Variety.mapPoints (heartCellInclusion G I w) h)).apply_symm_apply _)
  · rintro ⟨s, rfl⟩
    let b' := stabilizerPointsEquiv (leviBorelVariety G I) (schubertCell G w)
      (Variety.mapPoints (heartCellInclusion G I w) h) s
    obtain ⟨t, ht, htb⟩ := heartLevi_stabilizer G I w hI h b'.val
      (MulAction.mem_stabilizer_iff.mp b'.property)
    let sp := (stabilizerPointsEquiv (torusVariety G) (heart G I w) h).symm
      ⟨t, MulAction.mem_stabilizer_iff.mpr ht⟩
    refine ⟨sp, ?_⟩
    rw [Variety.mapPoints_comp]
    have hs := congrArg Subtype.val
      ((stabilizerPointsEquiv (torusVariety G) (heart G I w) h).apply_symm_apply
        ⟨t, MulAction.mem_stabilizer_iff.mpr ht⟩)
    change Variety.mapPoints (torusLeviBorelInclusion G I)
      (Variety.mapPoints (stabilizerInclusion (torusVariety G) (heart G I w) h) sp) = _
    rw [show Variety.mapPoints (stabilizerInclusion (torusVariety G) (heart G I w) h) sp = t
      from hs]
    exact htb

/-- At a heart point the torus and Levi--Borel stabilizer varieties are isomorphic. -/
def heartStabilizerIso (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
    (h : (heart G I w).points) :
    (stabilizerVariety (torusVariety G) (heart G I w) h).toOver ≅
      (stabilizerVariety (leviBorelVariety G I) (schubertCell G w)
        (Variety.mapPoints (heartCellInclusion G I w) h)).toOver := by
  have : IsClosedImmersion (stabilizerInclusion (torusVariety G) (heart G I w) h ≫
      torusLeviBorelInclusion G I).left := by
    change IsClosedImmersion ((stabilizerInclusion (torusVariety G) (heart G I w) h).left ≫
      (torusLeviBorelInclusion G I).left)
    infer_instance
  exact Variety.pointImageIso
    (stabilizerInclusion (torusVariety G) (heart G I w) h ≫ torusLeviBorelInclusion G I)
    (stabilizerInclusion (leviBorelVariety G I) (schubertCell G w)
      (Variety.mapPoints (heartCellInclusion G I w) h)) (heartStabilizer_range G I w hI h)

end SchubertOrbits
