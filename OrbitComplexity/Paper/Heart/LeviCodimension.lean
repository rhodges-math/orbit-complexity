import OrbitComplexity.Paper.Heart.LeviStabilizer
import OrbitComplexity.SchubertGeometry.Levi.Dimension
import OrbitComplexity.GroupActions.Actions.OrbitDimensionGeneral

/-! # Codimensions of Levi--Borel orbits

The torus and Levi--Borel stabilizers at a heart point have equal dimensions.
The group-dimension difference is the parabolic-cell dimension, which cancels
the same difference in the ambient cells.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem natDim_add {X Y Z : Variety K}
    [Nonempty X.scheme] [Nonempty Y.scheme] [Nonempty Z.scheme]
    (h : X.dim = Y.dim + Z.dim) : X.natDim = Y.natDim + Z.natDim := by
  rw [← X.natDim_cast, ← Y.natDim_cast, ← Z.natDim_cast] at h
  have he : (X.natDim : WithBot ℕ∞) = ((Y.natDim + Z.natDim : ℕ) : WithBot ℕ∞) := by
    simpa only [Nat.cast_add] using h
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp he)

omit [IsAlgClosed K] [CharZero K] in
private theorem natDim_of_iso {X Y : Variety K} [Nonempty X.scheme] [Nonempty Y.scheme]
    (e : X.toOver ≅ Y.toOver) : X.natDim = Y.natDim := by
  have h := Variety.dim_eq_of_iso X e
  rw [← X.natDim_cast, ← Y.natDim_cast] at h
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp h)

private theorem cell_heart_dim_add (I : Set G.rootBase.support) (w : G.weylGroup) :
    (schubertCell G w).dim =
      (schubertCell G (leftParabolicFactor G.rootBase I w)).dim + (heart G I w).dim := by
  have hh := Variety.dim_eq_of_iso (heart G I w) (heartMinimalIso G I w)
  rw [hh, schubertCell_dim, schubertCell_dim, schubertCell_dim]
  simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : WithBot ℕ∞))
    (RootInversionCount.leftParabolic_decomposition G.rootBase I w)

private theorem leviBorel_dim_add (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i)) :
    (leviBorelVariety G I).dim = (torusVariety G).dim +
      (schubertCell G (leftParabolicFactor G.rootBase I w)).dim := by
  rw [leviBorelVariety_dim]
  congr 1
  have ha := (leftFactor_longest_iff G.rootBase I w).2.mpr hI
  have hroot : leftRootInversionIndices G.rootBase (leftParabolicFactor G.rootBase I w) =
      leviPositiveRoots G.rootBase I := by rw [ha, leftRootInv_longestParabolic]
  simpa only [hroot] using Variety.dim_eq_of_iso
    (rootSubsetVariety G _ (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _))
    (schubertCellIso G (leftParabolicFactor G.rootBase I w))

/-- Inclusion of the heart preserves orbit codimension from the torus to the Levi--Borel group. -/
theorem heartLeviOrbitCodim (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
    (h : (heart G I w).points) :
    orbitCodim (leviBorelVariety G I) (schubertCell G w)
        (Variety.mapPoints (heartCellInclusion G I w) h) =
      orbitCodim (torusVariety G) (heart G I w) h := by
  have : Nonempty (heart G I w).scheme := ⟨(heart G I w).pointMap h⟩
  have : Nonempty (schubertCell G w).scheme := ⟨(schubertCell G w).pointMap
    (Variety.mapPoints (heartCellInclusion G I w) h)⟩
  have : Nonempty (schubertCell G (leftParabolicFactor G.rootBase I w)).scheme :=
    ⟨(schubertCell G _).pointMap
      (Variety.mapPoints (schubertCellIso G (leftParabolicFactor G.rootBase I w)).hom 1)⟩
  have : Nonempty (leviBorelVariety G I).scheme := ⟨(leviBorelVariety G I).pointMap 1⟩
  have : Nonempty (torusVariety G).scheme := ⟨(torusVariety G).pointMap 1⟩
  have hc := natDim_add (cell_heart_dim_add G I w)
  have hb := natDim_add (leviBorel_dim_add G I w hI)
  have hs := natDim_of_iso (heartStabilizerIso G I w hI h)
  have hoB := dim_orbit (leviBorelVariety G I) (schubertCell G w)
    (Variety.mapPoints (heartCellInclusion G I w) h)
  have hoT := dim_orbit (torusVariety G) (heart G I w) h
  unfold orbitCodim
  rw [hoB, hoT, hc, hb, ← hs]
  omega

/-- Parabolic translation preserves codimension from minimal-cell torus to Levi--Borel orbits. -/
theorem cellLeviOrbitCodim (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
    (x : (schubertCell G (leftParabolicRepresentative G.rootBase I w)).points) :
    orbitCodim (leviBorelVariety G I) (schubertCell G w)
        (Variety.mapPoints (heartCellInclusion G I w)
          (Variety.mapPoints (heartTranslationIso G I w).hom x)) =
      orbitCodim (torusVariety G)
        (schubertCell G (leftParabolicRepresentative G.rootBase I w)) x :=
  (heartLeviOrbitCodim G I w hI _).trans (cellHeartOrbitCodim G I w x)

end SchubertOrbits
