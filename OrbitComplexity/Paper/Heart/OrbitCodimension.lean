import OrbitComplexity.Paper.Heart.OrbitBounds
import OrbitComplexity.Paper.Heart.TorusCodimension
import OrbitComplexity.SchubertGeometry.Cells.OrbitDecompositionDimension
import OrbitComplexity.Paper.Heart.Meeting

/-! # Stabilizer and parabolic length formulas for Levi--Borel orbit codimension -/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
  Topology BruhatIntervals
universe u

private theorem orbitNatDim_eq_of_mem {K : Type u} [Field K]
    (L X : Variety K) [GrpObj L.toOver] [ModObj L.toOver X.toOver]
    {x y : X.points} (h : y ∈ MulAction.orbit L.points x) :
    orbitNatDim L X y = orbitNatDim L X x := by
  have he : MulAction.orbit L.points y = MulAction.orbit L.points x :=
    MulAction.orbit_eq_iff.mpr h
  unfold orbitNatDim orbitDim
  rw [he]

private theorem natDim_add {K : Type u} [Field K] {X Y Z : Variety K}
    [Nonempty X.scheme] [Nonempty Y.scheme] [Nonempty Z.scheme]
    (h : X.dim = Y.dim + Z.dim) : X.natDim = Y.natDim + Z.natDim := by
  rw [← X.natDim_cast, ← Y.natDim_cast, ← Z.natDim_cast] at h
  have he : (X.natDim : WithBot ℕ∞) = ((Y.natDim + Z.natDim : ℕ) : WithBot ℕ∞) := by
    simpa only [Nat.cast_add] using h
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp he)

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

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

/-- Stabilizers, group dimensions and parabolic lengths give the full orbit-codimension chain. -/
theorem levi_orbit_codimension_chain (I : Set G.rootBase.support) (w : G.weylGroup)
    (q : (schubertCell G w).points) (h : (heart G I w).points)
    (hq : Variety.mapPoints (heartCellInclusion G I w) h ∈
      MulAction.orbit (leviBorelVariety G I).points q) :
    let cs := weylCoxeterSystem G.rootBase
    let a := leftParabolicFactor G.rootBase I w
    let d := leftParabolicRepresentative G.rootBase I w
    let n := longestParabolicElement G.rootBase I
    let y := Variety.mapPoints (heartCellInclusion G I w) h
    let B := leviBorelVariety G I
    let T := torusVariety G
    let S := stabilizerVariety T (heart G I w) h
    let R := stabilizerVariety B (schubertCell G w) y
    (orbitNatDim B (schubertCell G w) q : ℤ) = (B.natDim : ℤ) - R.natDim ∧
    (S.natDim : ℤ) ≤ R.natDim ∧
    cs.length w = cs.length a + cs.length d ∧
    B.natDim = T.natDim + cs.length n ∧
    (orbitNatDim T (heart G I w) h : ℤ) = (T.natDim : ℤ) - S.natDim ∧
    (cs.length w : ℤ) - orbitNatDim B (schubertCell G w) q ≥
      (cs.length w : ℤ) - B.natDim + S.natDim ∧
    (cs.length w : ℤ) - B.natDim + S.natDim =
      (cs.length a : ℤ) + cs.length d - (T.natDim + cs.length n) + S.natDim ∧
    (cs.length a : ℤ) + cs.length d - (T.natDim + cs.length n) + S.natDim =
      (cs.length d : ℤ) - ((T.natDim : ℤ) - S.natDim) -
        ((cs.length n : ℤ) - cs.length a) ∧
    (cs.length d : ℤ) - ((T.natDim : ℤ) - S.natDim) -
        ((cs.length n : ℤ) - cs.length a) =
      (cs.length d : ℤ) - orbitNatDim T (heart G I w) h -
        ((cs.length n : ℤ) - cs.length a) ∧
    (cs.length w : ℤ) - orbitNatDim B (schubertCell G w) q ≥
      (cs.length d : ℤ) - orbitNatDim T (heart G I w) h -
        ((cs.length n : ℤ) - cs.length a) := by
  let y := Variety.mapPoints (heartCellInclusion G I w) h
  have ho := orbitNatDim_eq_of_mem (leviBorelVariety G I) (schubertCell G w) hq
  have hb := groupNatDim_eq_orbit_add (leviBorelVariety G I) (schubertCell G w) y
  have ht := groupNatDim_eq_orbit_add (torusVariety G) (heart G I w) h
  have hB := leviBorel_natDim G I
  have hl : (weylCoxeterSystem G.rootBase).length w =
      (weylCoxeterSystem G.rootBase).length (leftParabolicFactor G.rootBase I w) +
      (weylCoxeterSystem G.rootBase).length
        (leftParabolicRepresentative G.rootBase I w) := by
    simpa only [weylCoxeterSystem_length] using
      RootInversionCount.leftParabolic_decomposition G.rootBase I w
  have hs := heartLevi_stabilizer_dim_le G I w h
  rw [← (stabilizerVariety (torusVariety G) (heart G I w) h).natDim_cast,
    ← (stabilizerVariety (leviBorelVariety G I) (schubertCell G w) y).natDim_cast] at hs
  have hsN : (stabilizerVariety (torusVariety G) (heart G I w) h).natDim ≤
      (stabilizerVariety (leviBorelVariety G I) (schubertCell G w) y).natDim := by
    exact_mod_cast hs
  dsimp only [y] at hb hsN
  dsimp only
  refine ⟨?_, ?_, hl, hB, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

end SchubertOrbits
