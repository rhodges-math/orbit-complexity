import OrbitComplexity.BruhatIntervals.Graph.Polytopes
import OrbitComplexity.Paper.Deodhar.Realization
import OrbitComplexity.Paper.Deodhar.Characters
import OrbitComplexity.SchubertGeometry.Cells.RichardsonMoment
import Batteries.Tactic.Lint

/-! # Spans and affine dimensions of Bruhat interval polytopes

For a finite reduced crystallographic root pairing over a characteristic-zero
field, twice rho and its real half-sum give interval polytopes whose point
differences span the interval labels. Their real affine dimensions equal
algebraic dimension. The root-pairing formulation includes the data of reductive
groups over algebraically closed characteristic-zero fields and over the complex
numbers. The half-sum is a real vector; no character-lattice condition is needed.

## References

* E. Tsukerman and L. Williams, *Bruhat interval polytopes*, Adv. Math. 285 (2015), 766–810,
  Definition 7.8.
-/

open ReductiveGroups BruhatIntervals
noncomputable section
namespace SchubertOrbits

/-- At twice rho, all differences from the lower endpoint of the interval
polytope span the interval labels, and its real affine dimension equals the
algebraic dimension of the Bruhat interval. -/
theorem interval_polytope_span_dimension
    {ι K M N : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {P : RootPairing ι K M N} [Fintype ι] [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (u v : P.weylGroup) (huv : (weylCoxeterSystem b).BruhatLE u v) :
    Submodule.span ℝ
        ((fun q => q - (weylRealization b).action u (realTwoRho b)) ''
          intervalPolytope (weylRealization b) u v (realTwoRho b)) =
      labelSpan (weylRealization b) u v ∧
    (affineSpan ℝ (intervalPolytope (weylRealization b) u v (realTwoRho b))).finDim =
      (algebraicDim (weylRealization b) u v : WithBot ℕ) := by
  constructor
  · exact @intervalPolytope_span_sub b.support P.weylGroup (b.support →₀ ℝ)
      (inferInstanceAs (Group P.weylGroup)) (simpleCoxeterMatrix b) (weylCoxeterSystem b)
      (inferInstanceAs (AddCommGroup (b.support →₀ ℝ)))
      (inferInstanceAs (Module ℝ (b.support →₀ ℝ))) (weylRealization b)
      u v huv (realTwoRho b) (realTwoRho_regular b)
  · exact @intervalPolytope_finDim b.support P.weylGroup (b.support →₀ ℝ)
      (inferInstanceAs (Group P.weylGroup)) (simpleCoxeterMatrix b) (weylCoxeterSystem b)
      (inferInstanceAs (AddCommGroup (b.support →₀ ℝ)))
      (inferInstanceAs (Module ℝ (b.support →₀ ℝ))) (weylRealization b)
      u v huv (realTwoRho b) (realTwoRho_regular b)

/-- The real half-sum interval polytope is the half-scaling of the twice-rho
polytope. Its differences span the same interval labels, and its real affine
dimension equals the algebraic dimension of the interval. -/
theorem interval_polytope_half_sum
    {ι K M N : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {P : RootPairing ι K M N} [Fintype ι] [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (u v : P.weylGroup) (huv : (weylCoxeterSystem b).BruhatLE u v) :
    intervalPolytope (weylRealization b) u v ((1 / 2 : ℝ) • realTwoRho b) =
        (fun q => (1 / 2 : ℝ) • q) ''
          intervalPolytope (weylRealization b) u v (realTwoRho b) ∧
    Submodule.span ℝ
        ((fun q => q - (weylRealization b).action u ((1 / 2 : ℝ) • realTwoRho b)) ''
          intervalPolytope (weylRealization b) u v ((1 / 2 : ℝ) • realTwoRho b)) =
      labelSpan (weylRealization b) u v ∧
    (affineSpan ℝ
        (intervalPolytope (weylRealization b) u v ((1 / 2 : ℝ) • realTwoRho b))).finDim =
      (algebraicDim (weylRealization b) u v : WithBot ℕ) := by
  have hregular (w : P.weylGroup)
      (α : {x : b.support →₀ ℝ // x ∈ (weylRealization b).positiveRoots}) :
      (weylRealization b).form α.val
        ((weylRealization b).action w ((1 / 2 : ℝ) • realTwoRho b)) ≠ 0 := by
    simpa only [LinearEquiv.map_smul, map_smul, smul_eq_mul] using
      mul_ne_zero (show (1 / 2 : ℝ) ≠ 0 by norm_num) (realTwoRho_regular b w α)
  refine ⟨?_, ?_, ?_⟩
  · exact @intervalPolytope_smul b.support P.weylGroup (b.support →₀ ℝ)
      (inferInstanceAs (Group P.weylGroup)) (simpleCoxeterMatrix b) (weylCoxeterSystem b)
      (inferInstanceAs (AddCommGroup (b.support →₀ ℝ)))
      (inferInstanceAs (Module ℝ (b.support →₀ ℝ))) (weylRealization b)
      u v (1 / 2 : ℝ) (realTwoRho b)
  · exact @intervalPolytope_span_sub b.support P.weylGroup (b.support →₀ ℝ)
      (inferInstanceAs (Group P.weylGroup)) (simpleCoxeterMatrix b) (weylCoxeterSystem b)
      (inferInstanceAs (AddCommGroup (b.support →₀ ℝ)))
      (inferInstanceAs (Module ℝ (b.support →₀ ℝ))) (weylRealization b)
      u v huv ((1 / 2 : ℝ) • realTwoRho b) hregular
  · exact @intervalPolytope_finDim b.support P.weylGroup (b.support →₀ ℝ)
      (inferInstanceAs (Group P.weylGroup)) (simpleCoxeterMatrix b) (weylCoxeterSystem b)
      (inferInstanceAs (AddCommGroup (b.support →₀ ℝ)))
      (inferInstanceAs (Module ℝ (b.support →₀ ℝ))) (weylRealization b)
      u v huv ((1 / 2 : ℝ) • realTwoRho b) hregular

section CharacterCoordinates
universe u
attribute [local instance] Classical.propDecidable
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem hull_image_eq {W A B : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] (f : A →ₗ[ℝ] B) (v : W → A) (w : W → B)
    (S : Set W) (h : ∀ x ∈ S, f (v x) = w x) :
    f '' convexHull ℝ (v '' S) = convexHull ℝ (w '' S) := by
  rw [f.image_convexHull, Set.image_image]
  congr 1
  exact Set.image_congr h

/-- Character coordinates realize the interval hull through the real character map. -/
theorem interval_polytope_characters (u v : G.weylGroup) :
    realCharacterMap G '' BruhatIntervals.intervalPolytope (weylRealization G.rootBase)
        u v (realTwoRho G.rootBase) =
      convexHull ℝ ((fun w : G.weylGroup => fun j =>
        (((∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
          G.rootCharacter (G.rootSystem.weylGroupToPerm w r)).toAdd) j : ℝ)) ''
        BruhatIntervals.bruhatInterval (weylCoxeterSystem G.rootBase) u v) := by
  exact @hull_image_eq G.weylGroup (G.rootBase.support →₀ ℝ) (G.torusIndex → ℝ)
    inferInstance inferInstance inferInstance inferInstance (realCharacterMap G)
    (fun w => (weylRealization G.rootBase).action w (realTwoRho G.rootBase))
    (fun w j => (((∏ r ∈ Finset.univ.filter G.rootBase.IsPos,
      G.rootCharacter (G.rootSystem.weylGroupToPerm w r)).toAdd) j : ℝ))
    (BruhatIntervals.bruhatInterval (weylCoxeterSystem G.rootBase) u v)
    (fun w _ => realCharacterMap_weyl_twoRho G w)

/-- In real torus character coordinates the interval hull has algebraic dimension. -/
theorem interval_polytope_character_dimension (u v : G.weylGroup)
    (huv : (weylCoxeterSystem G.rootBase).BruhatLE u v) :
    (affineSpan ℝ (realCharacterMap G ''
      BruhatIntervals.intervalPolytope (weylRealization G.rootBase)
        u v (realTwoRho G.rootBase))).finDim =
      (BruhatIntervals.algebraicDim (weylRealization G.rootBase) u v : WithBot ℕ) := by
  have hm := AffineSubspace.finDim_map_of_injective
    (f := (realCharacterMap G).toAffineMap) (realCharacterMap_injective G)
    (affineSpan ℝ (BruhatIntervals.intervalPolytope (weylRealization G.rootBase)
      u v (realTwoRho G.rootBase)))
  rw [AffineSubspace.map_span] at hm
  exact hm.trans (interval_polytope_span_dimension G.rootBase u v huv).2

end CharacterCoordinates


open CategoryTheory AlgebraicGeometry GroupActions SchubertGeometry

/-- Complex Richardson torus orbits have interval algebraic dimension as their attained
maximum dimension. The proof uses their adjoint moment polytopes. -/
theorem richardson_max_orbit_complex (G : ReductiveGroupData ℂ) (a b : G.weylGroup)
    (hab : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    (∀ x : (richardsonVariety G a b).points,
      orbitDim (torusVariety G) (richardsonVariety G a b) x ≤
        (algebraicDim (weylRealization G.rootBase) a b : WithBot ℕ∞)) ∧
    ∃ x : (richardsonVariety G a b).points,
      orbitDim (torusVariety G) (richardsonVariety G a b) x =
        (algebraicDim (weylRealization G.rootBase) a b : WithBot ℕ∞) := by
  classical
  let : Fintype G.torusIndex := Fintype.ofFinite G.torusIndex
  have hData := @exists_richardson_moment_map G
  obtain ⟨_w, _hw, _hB, _hdet, _hWeyl, hDim, hAll⟩ := hData
  have hRich := hAll a b ((weyl_bruhat_iff G.rootBase a b).mpr hab)
  obtain ⟨hSub, ⟨xGen, hGen, _hCoords, _hClosure⟩, _hImage⟩ := hRich
  have hQDim := @interval_polytope_character_dimension ℂ inferInstance inferInstance
    inferInstance G a b hab
  rw [interval_polytope_characters G a b] at hQDim
  have hQDim' := congrArg (WithBot.map (fun n : ℕ => (n : ℕ∞))) hQDim
  have hmap : Monotone (fun n : ℕ => (n : ℕ∞)) :=
    fun _ _ h => ENat.natCast_le_natCast.mpr h
  have hR (x : (richardsonVariety G a b).points) :
      orbitDim (torusVariety G) (richardsonVariety G a b) x =
        orbitDim (torusVariety G) (flagVariety G)
          (Variety.mapPoints (richardsonInclusion G a b) x) :=
    @orbitDim_of_injective_points ℂ inferInstance (torusVariety G)
      (richardsonVariety G a b) (flagVariety G) inferInstance inferInstance inferInstance
      inferInstance inferInstance (richardsonInclusion G a b) inferInstance
      (Variety.mapPoints_injective_of_mono (richardsonInclusion G a b)) x
  constructor
  · intro x
    have hSpan := affineSpan_mono ℝ (hSub x)
    have hFinite := AffineSubspace.finDim_mono hSpan
    exact le_of_eq_of_le ((hR x).trans
      (hDim (Variety.mapPoints (richardsonInclusion G a b) x)))
      ((hmap.withBot_map hFinite).trans_eq hQDim')
  · refine ⟨xGen, ?_⟩
    have hFull := congrArg (fun S : Set (G.torusIndex → ℝ) =>
      WithBot.map (fun n : ℕ => (n : ℕ∞)) (affineSpan ℝ S).finDim) hGen
    exact (hR xGen).trans ((hDim (Variety.mapPoints (richardsonInclusion G a b) xGen)).trans
      (hFull.trans hQDim'))

/-- The maximum natural dimension of a complex Richardson torus orbit is the interval
algebraic dimension. -/
theorem richardson_orbit_maximum_complex (G : ReductiveGroupData ℂ) (a b : G.weylGroup)
    (hab : (weylCoxeterSystem G.rootBase).BruhatLE a b) :
    IsGreatest {n : ℕ | ∃ x : (richardsonVariety G a b).points,
      orbitNatDim (torusVariety G) (richardsonVariety G a b) x = n}
      (algebraicDim (weylRealization G.rootBase) a b) := by
  have hMax := richardson_max_orbit_complex G a b hab
  constructor
  · obtain ⟨x, hx⟩ := hMax.2
    refine ⟨x, ?_⟩
    have hc := (orbitNatDim_cast (torusVariety G) (richardsonVariety G a b) x).trans hx
    exact ENat.natCast_inj.mp (WithBot.coe_injective hc)
  · rintro n ⟨x, rfl⟩
    have hc := le_of_eq_of_le
      (orbitNatDim_cast (torusVariety G) (richardsonVariety G a b) x) (hMax.1 x)
    exact ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp hc)

end SchubertOrbits
