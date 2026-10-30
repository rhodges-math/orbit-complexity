import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTorsionTorus

/-!
# Diagonalizable Torus Factor

Every Hopf morphism from a finite-type diagonalizable group to a
torus factors through its canonical torsion-free torus subgroup. -/

noncomputable section
namespace ReductiveGroups

universe u v
variable {K M : Type u} {L : Type v} [Field K] [CommGroup M] [CommGroup L]
  [IsMulTorsionFree L]

/-- Factor a bialgebra morphism to a torsion-free diagonalizable
coordinate algebra through the universal torsion quotient. -/
def diagonalizableTorusCoordinateFactor
    (π : MonoidAlgebra K M →ₐc[K] MonoidAlgebra K L) :
    MonoidAlgebra K (M ⧸ CommGroup.torsion M) →ₐc[K] MonoidAlgebra K L :=
  MonoidAlgebra.mapDomainBialgHom K
    (torsionFreeFactor (MonoidAlgebra.mapDomainOfBialgHom π))

/-- The equality is

```lean
(diagonalizableTorusCoordinateFactor π).comp torsionFreeCoordinateMap = π
```
-/
theorem diagonalizableTorusCoordinateFactor_comp
    (π : MonoidAlgebra K M →ₐc[K] MonoidAlgebra K L) :
    (diagonalizableTorusCoordinateFactor π).comp torsionFreeCoordinateMap = π := by
  change (MonoidAlgebra.mapDomainBialgHom K
    (torsionFreeFactor (MonoidAlgebra.mapDomainOfBialgHom π))).comp
      torsionFreeCoordinateMap = π
  rw [← mapDomainBialgHom_factor_torsionFree,
    MonoidAlgebra.mapDomainBialgHom_mapDomainOfBialgHom]

/-- The map is surjective:

```lean
Function.Surjective (diagonalizableTorusCoordinateFactor π)
```
-/
theorem DiagonalizableTorusCoordinateFactor.surjective
    (π : MonoidAlgebra K M →ₐc[K] MonoidAlgebra K L)
    (hπ : Function.Surjective π) :
    Function.Surjective (diagonalizableTorusCoordinateFactor π) := by
  intro y
  obtain ⟨x, hx⟩ := hπ y
  exact ⟨torsionFreeCoordinateMap x,
    (congrArg (fun f : MonoidAlgebra K M →ₐc[K] MonoidAlgebra K L => f x)
      (diagonalizableTorusCoordinateFactor_comp π)).trans hx⟩

/-- The torus's defining ideal contains the canonical torus ideal,
so its closed subgroup lies inside the canonical torus of `D(M)`. -/
theorem torsionFreeTorusIdeal_le_ker
    (π : MonoidAlgebra K M →ₐc[K] MonoidAlgebra K L) :
    (torsionFreeTorusIdeal (K := K) (M := M)).toIdeal ≤
      RingHom.ker (π : MonoidAlgebra K M →ₐ[K] MonoidAlgebra K L) := by
  intro a ha
  have hq : torsionFreeCoordinateMap (K := K) (M := M) a = 0 := by
    exact (TauCeti.HopfIdeal.mem_kerOfSurjective _ _).mp ha
  apply RingHom.mem_ker.mpr
  have h := congrArg (fun f : MonoidAlgebra K M →ₐc[K] MonoidAlgebra K L => f a)
    (diagonalizableTorusCoordinateFactor_comp π)
  change diagonalizableTorusCoordinateFactor π (torsionFreeCoordinateMap a) = π a at h
  rw [hq, map_zero] at h
  change π a = 0
  exact h.symm

/-- For a closed target torus, containment is an inequality of the
Hopf ideals defining the two closed subgroups. -/
theorem TorsionFreeTorusIdeal.le_kernelOfSurjective
    (π : MonoidAlgebra K M →ₐc[K] MonoidAlgebra K L)
    (hπ : Function.Surjective π) :
    torsionFreeTorusIdeal (K := K) (M := M) ≤
      TauCeti.HopfIdeal.kerOfSurjective π hπ := by
  apply TauCeti.HopfIdeal.toIdeal_le_toIdeal.mp
  simpa only [TauCeti.HopfIdeal.kerOfSurjective_toIdeal] using
    torsionFreeTorusIdeal_le_ker π

end ReductiveGroups
