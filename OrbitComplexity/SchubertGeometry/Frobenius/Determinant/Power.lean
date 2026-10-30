import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.LeftUnipotent

/-! # Powers of the normalized determinant coefficient -/

open ReductiveGroups TauCeti GroupActions WithConv
open scoped TensorProduct

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private theorem character_power (chi : G.characters) (N : ℕ) :
    borelCharacterMap G (chi ^ N) (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) =
      borelCharacterMap G chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) ^ N := by
  obtain ⟨z, _, hz⟩ := borelCharacterMap_points G (AlgHom.id K G.borelAlgebra)
  have hchi : borelCharacterMap G chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) =
      z (MonoidAlgebra.single chi 1) := by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply, BialgHom.coe_toAlgHom] using hz chi
  calc
    _ = z (MonoidAlgebra.single (chi ^ N) 1) := by
      simpa only [AlgHom.comp_apply, AlgHom.id_apply, BialgHom.coe_toAlgHom] using hz (chi ^ N)
    _ = z (MonoidAlgebra.single chi 1) ^ N := by
      symm
      rw [← map_pow, MonoidAlgebra.single_pow, one_pow]
    _ = _ := congrArg (fun x => x ^ N) hchi.symm

/-- The degree parameter is an integral power of one fixed regular coefficient. -/
def positiveDetPower (N : ℕ) : G.coordinateAlgebra :=
  positiveDetCoefficient G ^ N

/-- Every degree retains the normalization at the identity. -/
theorem positiveDetPower_counit (N : ℕ) :
    Coalgebra.counit (R := K) (A := G.coordinateAlgebra) (positiveDetPower G N) = 1 := by
  change (Bialgebra.counitAlgHom K G.coordinateAlgebra) (positiveDetCoefficient G ^ N) = 1
  rw [map_pow]
  change (Coalgebra.counit (R := K) (A := G.coordinateAlgebra)
    (positiveDetCoefficient G)) ^ N = 1
  rw [positiveDet_counit, one_pow]

/-- The right Borel coaction has the full character equal to the corresponding power of delta. -/
theorem positiveDetPower_right_coaction (N : ℕ) :
    (Algebra.TensorProduct.map (AlgHom.id K G.coordinateAlgebra)
      ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom).toAlgHom)
        (Bialgebra.comulAlgHom K G.coordinateAlgebra (positiveDetPower G N)) =
      positiveDetPower G N ⊗ₜ[K]
        borelCharacterMap G (G.positiveRootCharacter ^ N)
          (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) := by
  dsimp only [positiveDetPower]
  rw [map_pow, map_pow]
  calc
    _ = (positiveDetCoefficient G ⊗ₜ[K]
        borelCharacterMap G G.positiveRootCharacter
          (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) ^ N :=
      congrArg (fun z : G.coordinateAlgebra ⊗[K] G.borelAlgebra => z ^ N)
        (positiveDet_right_coaction G)
    _ = (positiveDetCoefficient G ^ N) ⊗ₜ[K]
        (borelCharacterMap G G.positiveRootCharacter
          (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) ^ N) :=
      Algebra.TensorProduct.tmul_pow _ _ N
    _ = _ := congrArg (fun z : G.borelAlgebra => (positiveDetCoefficient G ^ N) ⊗ₜ[K] z)
      (character_power G G.positiveRootCharacter N).symm

/-- Restricting the same regular coefficient to the Borel gives its full character. -/
theorem positiveDetPower_borel_restriction (N : ℕ) :
    ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom)
        (positiveDetPower G N) =
      borelCharacterMap G (G.positiveRootCharacter ^ N)
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1) := by
  dsimp only [positiveDetPower]
  rw [map_pow]
  exact (congrArg (fun z : G.borelAlgebra => z ^ N)
    (positiveDet_borel_restriction G)).trans
      (character_power G G.positiveRootCharacter N).symm

/-- Left multiplication by the opposite unipotent group preserves every degree. -/
theorem positiveDetPower_left_unipotent (N : ℕ) (u g : G.points)
    (hu : u ∈ G.oppositeUnipotentPoints) :
    (u * g).ofConv (positiveDetPower G N) = g.ofConv (positiveDetPower G N) := by
  simp only [positiveDetPower, map_pow, positiveDet_left_unipotent G u g hu]

end SchubertGeometry.DeterminantSection
