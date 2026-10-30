import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelTangent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.ReductiveTorusRootSystem
import OrbitComplexity.ReductiveGroups.Groups.Tangents.SurjectiveTangentDescent
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CenterQuotientSolvablePullback
import OrbitComplexity.ReductiveGroups.Lie.Solvable.SolvableCartanCompatibleBase

/-!
# Borel Compatible Base

The fixed geometric Borel selects a compatible base of the
center-quotient Cartan root system. The center quotient has a nondegenerate Killing form. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

omit [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B] [Finite ι] in
/-- The fixed original Borel contains the torus tangent, including
after the center quotient. -/
theorem borel_centerQuotientTorus_le
    (I J : TauCeti.HopfIdeal K B) (hJI : J ≤ I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal) :
    (diagonalizableTangentImage π).map
      (centerQuotientLieHom (K := K)) ≤
    ((TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range).map
        (centerQuotientLieHom (K := K)) := by
  have hbase : diagonalizableTangentImage π ≤
      (TauCeti.derivationCompLieHom (B := K)
        (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range := by
    intro d hd
    apply (tangent_mem_hopfQuotient_iff J d).mpr
    intro a ha
    exact (tangent_mem_range_iff_kills_kernel π hπ d).mp hd a
      ((hker a).2 (hJI ha))
  intro y hy
  obtain ⟨d, hd, rfl⟩ :=
    ((diagonalizableTangentImage π).mem_map (centerQuotientLieHom (K := K)) y).mp hy
  exact (((TauCeti.derivationCompLieHom (B := K)
    (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range).mem_map
      (centerQuotientLieHom (K := K)) _).mpr ⟨d, hbase hd, rfl⟩

/-- The root support of the fixed original Borel image is positive for a
base of the fixed torus Cartan root system in the center quotient. -/
theorem BorelCompatibleBase.exists_centerQuotientBase
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (J : TauCeti.HopfIdeal K B)
    (hJ : TauCeti.HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (hJI : J ≤ I) :
    let q := centerQuotientLieHom (K := K) (L := 𝔤)
    let H := (diagonalizableTangentImage π).map q
    let S := ((TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range).map q
    letI : FiniteDimensional K 𝔤 := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI : IsKilling K (𝔤 ⧸ LieAlgebra.center K 𝔤) :=
      ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI : H.IsCartanSubalgebra :=
      ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    ∃ b : (rootSystem H).Base,
      ∀ α : H.root,
        (∀ z : 𝔤 ⧸ LieAlgebra.center K 𝔤,
          z ∈ rootSpace H α.val → z ∈ S) → b.IsPos α := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
  let _ := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan
    I hI π hπ hker hB
  let q := centerQuotientLieHom (K := K) (L := 𝔤)
  let H := (diagonalizableTangentImage π).map q
  let S := ((TauCeti.derivationCompLieHom (B := K)
    (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range).map q
  have hS : S = (q.comp
      (TauCeti.derivationCompLieHom (B := K)
        (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range.incl).range := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ :=
        ((TauCeti.derivationCompLieHom (B := K)
          (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range).mem_map q z
          |>.mp hz
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact (((TauCeti.derivationCompLieHom (B := K)
        (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range).mem_map q _).mpr
        ⟨y, y.property, rfl⟩
  let _ : LieAlgebra.IsSolvable S := by
    rw [hS]
    let _ := borel_tangentImage_isSolvable J hJ
    infer_instance
  have hHS : H ≤ S := borel_centerQuotientTorus_le I J hJI π hπ hker
  obtain ⟨b, hb⟩ := SolvableCartanCompatibleBase.exists_base_for_solvable_cartan_support H S hHS
  refine ⟨b, ?_⟩
  intro α hα
  apply hb α
  intro z hz
  exact hα z hz

end ReductiveGroups
