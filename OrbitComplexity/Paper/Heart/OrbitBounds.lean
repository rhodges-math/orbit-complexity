import OrbitComplexity.Paper.Heart.LeviOrbitDimension
import OrbitComplexity.GroupActions.Actions.StabilizerImages

/-! # Bounds for Levi--Borel cell orbit dimensions

Torus stabilizers embed in Levi--Borel stabilizers at heart points.
The group dimension formula and parabolic root count bound every cell orbit.
-/

set_option maxHeartbeats 400000
noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
  Topology BruhatIntervals
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem heartCell_torus (I : Set G.rootBase.support) (w : G.weylGroup)
    (t : (torusVariety G).points) (h : (heart G I w).points) :
    Variety.mapPoints (heartCellInclusion G I w) (t • h) =
      Variety.mapPoints (torusLeviBorelInclusion G I) t •
        Variety.mapPoints (heartCellInclusion G I w) h := by
  apply Variety.mapPoints_injective_of_mono (schubertCellInclusion G w)
  rw [← Variety.mapPoints_comp, heartCellInclusion_comp, leviBorelCell_smul,
    ← Variety.mapPoints_comp, heartCellInclusion_comp]
  obtain ⟨f, hf⟩ := (flagVarietyPointsEquiv G).surjective
    (Variety.mapPoints (heartInclusion G I w) h)
  have ht : Variety.mapPoints (torusLeviBorelInclusion G I) t •
      Variety.mapPoints (heartInclusion G I w) h =
      t • Variety.mapPoints (heartInclusion G I w) h := by
    rw [← hf, leviBorelFlag_smul, torusFlag_smul, flagVarietyAction_points,
      torusLeviBorelInclusion_points]
  rw [ht]
  exact heart_torus_smul G I w t h

/-- A torus stabilizer at a heart point maps into its Levi--Borel stabilizer. -/
theorem heartLevi_stabilizer_le (I : Set G.rootBase.support) (w : G.weylGroup)
    (h : (heart G I w).points) :
    (MulAction.stabilizer (torusVariety G).points h).map
        (Variety.mapPointsHom (torusLeviBorelInclusion G I)) ≤
      MulAction.stabilizer (leviBorelVariety G I).points
        (Variety.mapPoints (heartCellInclusion G I w) h) := by
  rintro _ ⟨t, ht, rfl⟩
  apply MulAction.mem_stabilizer_iff.mpr
  exact (heartCell_torus G I w t h).symm.trans
    (congrArg (Variety.mapPoints (heartCellInclusion G I w))
      (MulAction.mem_stabilizer_iff.mp ht))

private theorem stabilizer_image_subset (I : Set G.rootBase.support) (w : G.weylGroup)
    (h : (heart G I w).points) :
    Set.range (Variety.mapPoints
        (stabilizerInclusion (torusVariety G) (heart G I w) h ≫
          torusLeviBorelInclusion G I)) ⊆
      Set.range (Variety.mapPoints (stabilizerInclusion (leviBorelVariety G I)
        (schubertCell G w) (Variety.mapPoints (heartCellInclusion G I w) h))) := by
  rintro _ ⟨s, rfl⟩
  rw [stabilizerInclusion_points_range]
  rw [Variety.mapPoints_comp]
  apply heartLevi_stabilizer_le G I w h
  exact ⟨_, (stabilizerPointsEquiv (torusVariety G) (heart G I w) h s).property, rfl⟩

/-- The torus stabilizer dimension is bounded by the Levi--Borel stabilizer dimension. -/
theorem heartLevi_stabilizer_dim_le (I : Set G.rootBase.support) (w : G.weylGroup)
    (h : (heart G I w).points) :
    (stabilizerVariety (torusVariety G) (heart G I w) h).dim ≤
      (stabilizerVariety (leviBorelVariety G I) (schubertCell G w)
        (Variety.mapPoints (heartCellInclusion G I w) h)).dim := by
  let f := stabilizerInclusion (torusVariety G) (heart G I w) h ≫
    torusLeviBorelInclusion G I
  let g := stabilizerInclusion (leviBorelVariety G I) (schubertCell G w)
    (Variety.mapPoints (heartCellInclusion G I w) h)
  have : IsClosedImmersion f.left := by
    change IsClosedImmersion ((stabilizerInclusion (torusVariety G) (heart G I w) h).left ≫
      (torusLeviBorelInclusion G I).left)
    infer_instance
  have hr : Set.range f.left ⊆ Set.range g.left :=
    Variety.range_subset_of_mapPoints f g (stabilizer_image_subset G I w h)
  exact f.left.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq.trans_le
    ((IsEmbedding.inclusion hr).isInducing.topologicalKrullDim_le.trans
      g.left.isEmbedding.toHomeomorph.symm.isHomeomorph.topologicalKrullDim_eq.le)

omit [IsAlgClosed K] [CharZero K] in
private theorem natDim_add {X Y Z : Variety K}
    [Nonempty X.scheme] [Nonempty Y.scheme] [Nonempty Z.scheme]
    (h : X.dim = Y.dim + Z.dim) : X.natDim = Y.natDim + Z.natDim := by
  rw [← X.natDim_cast, ← Y.natDim_cast, ← Z.natDim_cast] at h
  have he : (X.natDim : WithBot ℕ∞) = ((Y.natDim + Z.natDim : ℕ) : WithBot ℕ∞) := by
    simpa only [Nat.cast_add] using h
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp he)

private theorem leviBorel_natDim (I : Set G.rootBase.support) :
    (leviBorelVariety G I).natDim = (torusVariety G).natDim +
      (weylCoxeterSystem G.rootBase).length (longestParabolicElement G.rootBase I) := by
  let v := longestParabolicElement G.rootBase I
  have : Nonempty (leviBorelVariety G I).scheme := ⟨(leviBorelVariety G I).pointMap 1⟩
  have : Nonempty (torusVariety G).scheme := ⟨(torusVariety G).pointMap 1⟩
  have : Nonempty (schubertCell G v).scheme := ⟨(schubertCell G v).pointMap
    (Variety.mapPoints (schubertCellIso G v).hom 1)⟩
  have hd : (leviBorelVariety G I).dim = (torusVariety G).dim + (schubertCell G v).dim := by
    rw [leviBorelVariety_dim]
    congr 1
    have he := Variety.dim_eq_of_iso (schubertUnipotent G v) (schubertCellIso G v)
    simpa only [schubertUnipotent, v, leftRootInv_longestParabolic] using he
  have hcell : (schubertCell G v).natDim = rootInversionCount G.rootBase v := by
    have he := (schubertCell G v).natDim_cast.trans (schubertCell_dim G v)
    exact ENat.natCast_inj.mp (WithBot.coe_inj.mp he)
  rw [← weylCoxeterSystem_length] at hcell
  exact (natDim_add hd).trans (congrArg ((torusVariety G).natDim + ·) hcell)

/-- A Levi--Borel orbit through the heart is bounded by the torus orbit and Levi root count. -/
theorem heartLeviOrbitDim_le (I : Set G.rootBase.support) (w : G.weylGroup)
    (h : (heart G I w).points) :
    orbitNatDim (leviBorelVariety G I) (schubertCell G w)
        (Variety.mapPoints (heartCellInclusion G I w) h) ≤
      (weylCoxeterSystem G.rootBase).length (longestParabolicElement G.rootBase I) +
        orbitNatDim (torusVariety G) (heart G I w) h := by
  have hs := heartLevi_stabilizer_dim_le G I w h
  rw [← (stabilizerVariety (torusVariety G) (heart G I w) h).natDim_cast,
    ← (stabilizerVariety (leviBorelVariety G I) (schubertCell G w)
      (Variety.mapPoints (heartCellInclusion G I w) h)).natDim_cast] at hs
  have hs' : (stabilizerVariety (torusVariety G) (heart G I w) h).natDim ≤
      (stabilizerVariety (leviBorelVariety G I) (schubertCell G w)
        (Variety.mapPoints (heartCellInclusion G I w) h)).natDim := by
    exact_mod_cast hs
  have hb := groupNatDim_eq_orbit_add (leviBorelVariety G I) (schubertCell G w)
    (Variety.mapPoints (heartCellInclusion G I w) h)
  have ht := groupNatDim_eq_orbit_add (torusVariety G) (heart G I w) h
  rw [leviBorel_natDim] at hb
  omega

end SchubertOrbits
