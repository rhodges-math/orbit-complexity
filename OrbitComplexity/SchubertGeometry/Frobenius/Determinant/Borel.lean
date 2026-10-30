import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Unipotent
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusPointCharacterValues

/-!
# Full Borel covariance of the constructed determinant coefficient

The scalar is calculated using the torus-times-unipotent factorization,
with the full positive-root character on that torus factor.
-/

open ReductiveGroups TauCeti GroupActions

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The Borel eigenvalue is evaluation of the normalized regular coefficient. -/
theorem positiveDet_borel_vector (b : G.points) (hb : b ∈ G.borelPoints) :
    letI := adjointExteriorComodule G
    Comodule.basePointsRepresentation (H := G.coordinateAlgebra) _ b
        (positiveDetVector G) =
      b.ofConv (positiveDetCoefficient G) • positiveDetVector G := by
  let := adjointExteriorComodule G
  obtain ⟨c, hc⟩ := positiveDet_borel_eigen G b hb
  have he : b.ofConv (positiveDetCoefficient G) = c := by
    change b.ofConv (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
      (positiveDetFunctional G) (positiveDetVector G)) = c
    rw [Comodule.apply_matrixCoefficient, hc, map_smul, positiveDet_pairing, smul_eq_mul,
      mul_one]
  rwa [he]

/-- Right translation by an Borel point multiplies by its determinant character. -/
theorem positiveDet_right_borel (g b : G.points) (hb : b ∈ G.borelPoints) :
    (g * b).ofConv (positiveDetCoefficient G) =
      b.ofConv (positiveDetCoefficient G) * g.ofConv (positiveDetCoefficient G) := by
  let := adjointExteriorComodule G
  change (g * b).ofConv (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
      (positiveDetFunctional G) (positiveDetVector G)) =
    b.ofConv (positiveDetCoefficient G) * g.ofConv
      (Comodule.matrixCoefficient (C := G.coordinateAlgebra)
        (positiveDetFunctional G) (positiveDetVector G))
  rw [Comodule.apply_matrixCoefficient, Comodule.apply_matrixCoefficient,
    map_mul, Module.End.mul_apply, positiveDet_borel_vector G b hb]
  simp only [map_smul, smul_eq_mul]

/-- Every Borel point has its T-U factorization, and the right-translation
scalar is the full delta value on that factor, including all central coordinates. -/
theorem positiveDet_borel_factor (b : G.points) (hb : b ∈ G.borelPoints) :
    ∃ (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K)) (u : G.points),
      u ∈ G.unipotentPoints ∧ b = TauCeti.AlgHom.mapDomain G.torusSplit z * u ∧
      b.ofConv (positiveDetCoefficient G) =
        z.ofConv (MonoidAlgebra.single G.positiveRootCharacter 1) ∧
      ∀ g : G.points, (g * b).ofConv (positiveDetCoefficient G) =
        z.ofConv (MonoidAlgebra.single G.positiveRootCharacter 1) *
          g.ofConv (positiveDetCoefficient G) := by
  obtain ⟨t, ht, u, hu, htu⟩ := BorelPoint.exists_torus_mul_borelRootUnipotent
    G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive b hb
  obtain ⟨z, hz⟩ := (mem_torusPoints_iff G.torusIdeal G.torusSplit
    G.split_surjective G.split_eq_zero t).mp ht
  have hfactor : TauCeti.AlgHom.mapDomain G.torusSplit z * u = b := by
    rw [← hz]
    exact htu
  have hval : b.ofConv (positiveDetCoefficient G) =
      z.ofConv (MonoidAlgebra.single G.positiveRootCharacter 1) := by
    rw [← hfactor, positiveDet_right_unipotent G _ u hu]
    have h1 : (1 : G.points).ofConv (positiveDetCoefficient G) = 1 := positiveDet_counit G
    simpa only [one_mul, h1, mul_one] using positiveDet_right_torus G 1 z
  refine ⟨z, u, hu, hfactor.symm, hval, ?_⟩
  intro g
  rw [positiveDet_right_borel G g b hb, hval]

end SchubertGeometry.DeterminantSection
