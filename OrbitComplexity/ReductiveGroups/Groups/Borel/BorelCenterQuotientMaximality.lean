import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTangentMaximality
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CenterQuotientSolvablePullback

/-!
# Borel Center Quotient Maximality

The image of the original Borel tangent remains maximal solvable in
the center quotient. Solvability is pulled back through the central
kernel before applying original geometric Borel maximality. -/

noncomputable section
namespace ReductiveGroups
open TauCeti CategoryTheory

universe u
variable {K B : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- The equality is

```lean
S = ((derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range).map
        (centerQuotientLieHom (K := K))
```
-/
theorem BorelCenterQuotientMaximality.centerQuotientImage_maximal_solvable
    (I J : HopfIdeal K B) (hJI : J ≤ I)
    (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))
    (S : LieSubalgebra K (𝔤 ⧸ LieAlgebra.center K 𝔤)) [LieAlgebra.IsSolvable S]
    (hJS : ((derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range).map
        (centerQuotientLieHom (K := K)) ≤ S) :
    S = ((derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range).map
        (centerQuotientLieHom (K := K)) := by
  let D := (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
  let q := centerQuotientLieHom (K := K) (L := 𝔤)
  let P := S.comap q
  let _ : LieAlgebra.IsSolvable P := centerQuotient_comap_isSolvable S
  have hDP : D ≤ P := (LieSubalgebra.map_le_iff_le_comap).mp hJS
  have hPD : P = D := BorelTangentMaximality.maximal_solvable_coordinateFree
    I J hJI hI hJ hB P hDP
  apply le_antisymm ?_ hJS
  intro z hz
  obtain ⟨d, rfl⟩ := centerQuotientLieHom_surjective (K := K) (L := 𝔤) z
  have hdP : d ∈ P := hz
  have hdD : d ∈ D := hPD ▸ hdP
  exact (D.mem_map q _).mpr ⟨d, hdD, rfl⟩

end ReductiveGroups
