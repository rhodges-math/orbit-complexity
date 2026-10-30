import OrbitComplexity.Paper.Heart.LeviOrbitStatements

/-! # Dimensions of Levi--Borel orbits through the heart

The orbit codimension equality and the parabolic dimension sum determine the
Levi--Borel orbit dimension from its torus orbit and parabolic factor.
-/

noncomputable section
namespace SchubertOrbits
open ReductiveGroups GroupActions SchubertGeometry CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem natDim_eq_count {X : Variety K} [Nonempty X.scheme] (n : ℕ)
    (hd : X.dim = (n : WithBot ℕ∞)) : X.natDim = n := by
  have he := X.natDim_cast.trans hd
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp he)

/-- A Levi--Borel orbit through the heart has the torus orbit dimension plus the factor length. -/
theorem heartLeviOrbitDim (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
    (h : (heart G I w).points) :
    orbitNatDim (leviBorelVariety G I) (schubertCell G w)
        (Variety.mapPoints (heartCellInclusion G I w) h) =
      (weylCoxeterSystem G.rootBase).length (leftParabolicFactor G.rootBase I w) +
        orbitNatDim (torusVariety G) (heart G I w) h := by
  have : Nonempty (heart G I w).scheme := ⟨(heart G I w).pointMap h⟩
  have : Nonempty (schubertCell G w).scheme := ⟨(schubertCell G w).pointMap
    (Variety.mapPoints (heartCellInclusion G I w) h)⟩
  have hw := natDim_eq_count (rootInversionCount G.rootBase w) (schubertCell_dim G w)
  have hh := natDim_eq_count
    (rootInversionCount G.rootBase (leftParabolicRepresentative G.rootBase I w))
    ((Variety.dim_eq_of_iso (heart G I w) (heartMinimalIso G I w)).trans
      (schubertCell_dim G _))
  have hdim := heartLeviOrbitCodim G I w hI h
  unfold orbitCodim at hdim
  rw [hw, hh] at hdim
  have hlen := RootInversionCount.leftParabolic_decomposition G.rootBase I w
  rw [weylCoxeterSystem_length]
  omega

/-- The Levi--Borel orbit dimension sum over the complex numbers. -/
theorem heartLeviOrbitDim_complex (G : ReductiveGroupData ℂ)
    (I : Set G.rootBase.support) (w : G.weylGroup)
    (hI : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
    (h : (heart G I w).points) :
    orbitNatDim (leviBorelVariety G I) (schubertCell G w)
        (Variety.mapPoints (heartCellInclusion G I w) h) =
      (weylCoxeterSystem G.rootBase).length (leftParabolicFactor G.rootBase I w) +
        orbitNatDim (torusVariety G) (heart G I w) h :=
  heartLeviOrbitDim G I w hI h

end SchubertOrbits
