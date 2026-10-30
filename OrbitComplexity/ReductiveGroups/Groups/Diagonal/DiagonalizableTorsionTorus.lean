import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTorsionTangent
import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTangentImage

/-!
# Diagonalizable Torsion Torus

The torsion-free quotient of the character group of a
diagonalizable group defines its canonical torus subgroup. -/

noncomputable section
namespace ReductiveGroups
open CategoryTheory

universe u
variable {K M : Type u} [Field K] [CharZero K] [CommGroup M] [Group.FG M]

private theorem torsionFreeCharacterLatticeEquiv :
    ∃ r : ℕ, Nonempty ((M ⧸ CommGroup.torsion M) ≃*
      Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) := by
  obtain ⟨r, ⟨e⟩⟩ := TorsionFreeCharacterGroup.exists_finLattice M
  exact ⟨r, ⟨e.trans (AddEquiv.toMultiplicative
    (Finsupp.domCongr Equiv.ulift.symm))⟩⟩

omit [CharZero K] in
/-- The exact torsion-free quotient coordinate algebra is a split torus. -/
theorem torsionFreeCoordinate_splitTorus :
    TauCeti.splitTorusCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K
        (MonoidAlgebra K (M ⧸ CommGroup.torsion M))) := by
  obtain ⟨r, ⟨e⟩⟩ := torsionFreeCharacterLatticeEquiv (M := M)
  rw [TauCeti.splitTorusCommHopfAlgProperty_iff]
  refine ⟨r, ?_⟩
  let f : TauCeti.DiagonalizableGroup.coordinateRing K
      (TauCeti.SplitTorus.characterGroup (ULift.{u} (Fin r))) ⟶
      TauCeti.FiniteTypeCommHopfAlgCat.of K
        (MonoidAlgebra K (M ⧸ CommGroup.torsion M)) :=
    TauCeti.FiniteTypeCommHopfAlgCat.ofHom
      (MonoidAlgebra.mapDomainBialgHom K e.symm.toMonoidHom)
  let g : TauCeti.FiniteTypeCommHopfAlgCat.of K
      (MonoidAlgebra K (M ⧸ CommGroup.torsion M)) ⟶
      TauCeti.DiagonalizableGroup.coordinateRing K
        (TauCeti.SplitTorus.characterGroup (ULift.{u} (Fin r))) :=
    TauCeti.FiniteTypeCommHopfAlgCat.ofHom
      (MonoidAlgebra.mapDomainBialgHom K e.toMonoidHom)
  refine ⟨{ hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · apply TauCeti.FiniteTypeCommHopfAlgCat.hom_ext
    change (MonoidAlgebra.mapDomainBialgHom K e.toMonoidHom).comp
      (MonoidAlgebra.mapDomainBialgHom K e.symm.toMonoidHom) = _
    rw [← MonoidAlgebra.mapDomainBialgHom_comp]
    simp
  · apply TauCeti.FiniteTypeCommHopfAlgCat.hom_ext
    change (MonoidAlgebra.mapDomainBialgHom K e.symm.toMonoidHom).comp
      (MonoidAlgebra.mapDomainBialgHom K e.toMonoidHom) = _
    rw [← MonoidAlgebra.mapDomainBialgHom_comp]
    simp

omit [CharZero K] in
/-- For these parameters,

```lean
TauCeti.torusCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K
        (MonoidAlgebra K (M ⧸ CommGroup.torsion M)))
```
-/
theorem torsionFreeCoordinate_torus :
    TauCeti.torusCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K
        (MonoidAlgebra K (M ⧸ CommGroup.torsion M))) :=
  (torsionFreeCoordinate_splitTorus (K := K) (M := M)).torus K _

/-- The ideal cutting out the torsion-free torus inside the original
diagonalizable group. -/
def torsionFreeTorusIdeal : TauCeti.HopfIdeal K (MonoidAlgebra K M) :=
  TauCeti.HopfIdeal.kerOfSurjective torsionFreeCoordinateMap
    torsionFreeCoordinateMap_surjective

omit [CharZero K] in
/-- The closed subgroup cut out by the kernel of the coordinate map
is a torus. -/
theorem torsionFreeTorusIdeal_isTorus :
    TauCeti.torusCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.of K (MonoidAlgebra K M))
        (torsionFreeTorusIdeal (K := K) (M := M))) := by
  let f : CommHopfAlgCat.of K (MonoidAlgebra K M) ⟶
      CommHopfAlgCat.of K (MonoidAlgebra K (M ⧸ CommGroup.torsion M)) :=
    CommHopfAlgCat.ofHom torsionFreeCoordinateMap
  let e : TauCeti.FiniteTypeCommHopfAlgCat.quotient
      (TauCeti.FiniteTypeCommHopfAlgCat.of K (MonoidAlgebra K M))
      (torsionFreeTorusIdeal (K := K) (M := M)) ≅
      TauCeti.FiniteTypeCommHopfAlgCat.of K
        (MonoidAlgebra K (M ⧸ CommGroup.torsion M)) :=
    ObjectProperty.isoMk _
      (TauCeti.CommHopfAlgCat.quotientKerOfSurjectiveIso f
        torsionFreeCoordinateMap_surjective)
  exact (TauCeti.torusCommHopfAlgProperty K).prop_of_iso e.symm
    (torsionFreeCoordinate_torus (K := K) (M := M))

omit [Group.FG M] in
/-- The torus inclusion preserves every original tangent direction. -/
theorem torsionFreeTorus_tangentImage_eq_top :
    diagonalizableTangentImage (torsionFreeCoordinateMap (K := K) (M := M)) = ⊤ := by
  exact (LieHom.range_eq_top _).mpr
    (TorsionFreeCoordinateMap.tangent_surjective (K := K) (M := M))

end ReductiveGroups
