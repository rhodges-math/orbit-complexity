import OrbitComplexity.ReductiveGroups.Groups.Tangents.SemisimpleTangentLattice
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTangentCharacters
import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap

/-!
# Diagonalizable Torsion Tangent

The torsion-free character quotient preserves the tangent space of
a diagonalizable group in characteristic zero. -/

noncomputable section
namespace ReductiveGroups

variable {K M : Type*} [Field K] [CharZero K] [CommGroup M]

/-- Coordinate map of the diagonalizable subgroup given by the universal
torsion-free quotient of its character group. -/
def torsionFreeCoordinateMap :
    MonoidAlgebra K M →ₐc[K]
      MonoidAlgebra K (M ⧸ CommGroup.torsion M) :=
  MonoidAlgebra.mapDomainBialgHom K (QuotientGroup.mk' (CommGroup.torsion M))

omit [CharZero K] in
/-- The equality is

```lean
Function.Surjective (torsionFreeCoordinateMap (K := K) (M := M))
```
-/
theorem torsionFreeCoordinateMap_surjective :
    Function.Surjective (torsionFreeCoordinateMap (K := K) (M := M)) := by
  intro x
  obtain ⟨p, hp⟩ := Finsupp.mapDomain_surjective
    (QuotientGroup.mk'_surjective (CommGroup.torsion M)) x.coeff
  refine ⟨MonoidAlgebra.ofCoeff p, ?_⟩
  apply MonoidAlgebra.coeff_injective
  change (MonoidAlgebra.mapDomain (QuotientGroup.mk' (CommGroup.torsion M))
    (MonoidAlgebra.ofCoeff p)).coeff = x.coeff
  simpa only [MonoidAlgebra.mapDomain, MonoidAlgebra.coeff_ofCoeff] using hp

/-- A tangent vector gives an additive character functional,
written as a multiplicative homomorphism into the additively tagged field. -/
def diagonalizableTangentCharacter
    (d : Derivation K (MonoidAlgebra K M)
      (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K)) :
    M →* Multiplicative K where
  toFun m := Multiplicative.ofAdd (characterDifferential m d)
  map_one' := by simp
  map_mul' a b := by
    change Multiplicative.ofAdd (characterDifferential (a * b) d) =
      Multiplicative.ofAdd (characterDifferential a d + characterDifferential b d)
    rw [characterDifferential_mul]
    rfl

omit [CharZero K] in
/-- The equality is

```lean
(diagonalizableTangentCharacter d m).toAdd = characterDifferential m d
```
-/
@[simp] theorem diagonalizableTangentCharacter_apply
    (d : Derivation K (MonoidAlgebra K M)
      (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K)) (m : M) :
    (diagonalizableTangentCharacter d m).toAdd = characterDifferential m d := rfl

omit [CharZero K] in
/-- Derivations at the counit of a diagonalizable group are determined by
their values on its monomial characters. -/
theorem diagonalizableTangent_ext
    (d e : Derivation K (MonoidAlgebra K M)
      (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K))
    (h : ∀ m : M, characterDifferential m d = characterDifferential m e) : d = e := by
  apply Derivation.ext
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m =>
      apply (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K
        (MonoidAlgebra K M) K).injective
      simpa only [MonoidAlgebra.of_apply, characterDifferential_apply] using h m
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul r x hx => simpa only [Derivation.map_smul] using congrArg (r • ·) hx

omit [CharZero K] in
/-- Character evaluation commutes with the differential of a domain map. -/
theorem CharacterDifferential.on_torsion_free_map
    (e : Derivation K (MonoidAlgebra K (M ⧸ CommGroup.torsion M))
      (TauCeti.Bialgebra.CounitAlgebra K
        (MonoidAlgebra K (M ⧸ CommGroup.torsion M)) K)) (m : M) :
    characterDifferential m
      (TauCeti.derivationComp (B := K) torsionFreeCoordinateMap e) =
    characterDifferential (QuotientGroup.mk' (CommGroup.torsion M) m) e := by
  rw [characterDifferential_apply, characterDifferential_apply,
    TauCeti.algEquivSelf_derivationComp_apply]
  change (TauCeti.Bialgebra.CounitAlgebra.algEquivSelf K
    (MonoidAlgebra K (M ⧸ CommGroup.torsion M)) K)
      (e (MonoidAlgebra.mapDomainBialgHom K
        (QuotientGroup.mk' (CommGroup.torsion M))
          (MonoidAlgebra.single m 1))) = _
  rw [MonoidAlgebra.mapDomainBialgHom_single]

/-- The differential of the torsion-free quotient is surjective:
all infinitesimal directions of a diagonalizable group survive. -/
theorem TorsionFreeCoordinateMap.tangent_surjective :
    Function.Surjective (TauCeti.derivationComp (B := K)
      (torsionFreeCoordinateMap (K := K) (M := M))) := by
  intro d
  let ψ := torsionFreeFactor (diagonalizableTangentCharacter d)
  refine ⟨diagonalizableTangentOfAdditive ψ, ?_⟩
  apply diagonalizableTangent_ext
  intro m
  rw [CharacterDifferential.on_torsion_free_map,
    CharacterDifferential.of_additive_tangent]
  change (torsionFreeFactor (diagonalizableTangentCharacter d)
    (QuotientGroup.mk m)).toAdd = characterDifferential m d
  rw [torsionFreeFactor_mk]
  rfl

/-- The torsion quotient induces an isomorphism on tangent spaces. -/
theorem TorsionFreeCoordinateMap.tangent_bijective :
    Function.Bijective (TauCeti.derivationComp (B := K)
      (torsionFreeCoordinateMap (K := K) (M := M))) :=
  ⟨TauCeti.derivationComp_injective_of_surjective _
      torsionFreeCoordinateMap_surjective,
    TorsionFreeCoordinateMap.tangent_surjective⟩

omit [CharZero K] in
/-- Every map of character groups into a torsion-free character group
factors its coordinate map through the same torsion quotient. -/
theorem mapDomainBialgHom_factor_torsionFree
    {N : Type*} [CommGroup N] [IsMulTorsionFree N] (f : M →* N) :
    MonoidAlgebra.mapDomainBialgHom K f =
      (MonoidAlgebra.mapDomainBialgHom K (torsionFreeFactor f)).comp
        torsionFreeCoordinateMap := by
  rw [torsionFreeCoordinateMap, ← MonoidAlgebra.mapDomainBialgHom_comp]
  congr 1

end ReductiveGroups
