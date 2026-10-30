import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusSplitPresentation
import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal

/-!
# Torus Coordinate Map

Split coordinates for the fixed torus subgroup. The ambient
Hopf algebra is unchanged, and the coordinate map has exactly its Hopf ideal. -/

noncomputable section
namespace ReductiveGroups
open CategoryTheory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A fixed torus quotient admits split coordinates with kernel exactly the
original subgroup's ideal. The ambient group is retained. -/
theorem exists_torusCoordinateMap
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K) (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.torusCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient B I)) :
    ∃ (n : ℕ) (π : B →ₐc[K]
        MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))),
      Function.Surjective π ∧ ∀ b : B, π b = 0 ↔ b ∈ I.toIdeal := by
  obtain ⟨n, ⟨e⟩⟩ := torus_split_of_isAlgClosed
    (TauCeti.FiniteTypeCommHopfAlgCat.quotient B I) hI
  let eb := (forget₂ (TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K)
    (CommHopfAlgCat.{u} K)).mapIso e
  let f := CommHopfAlgCat.ofIso eb.symm
  let q := (TauCeti.CommHopfAlgCat.mkQuotient B.obj I).hom
  refine ⟨n, f.toBialgHom.comp q, ?_, ?_⟩
  · exact f.surjective.comp (TauCeti.CommHopfAlgCat.mkQuotient_surjective B.obj I)
  · intro b
    change f (q b) = 0 ↔ b ∈ I.toIdeal
    have hz : f (q b) = 0 ↔ q b = 0 :=
      ⟨fun h => f.injective (h.trans (map_zero f).symm), fun h => h ▸ map_zero f⟩
    exact hz.trans (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff B.obj I b)

/-- In particular, the fixed maximal torus from the orbit problem supplies
the required coordinate map; maximality is not a substitute for splitting. -/
theorem exists_maximalTorusCoordinateMap
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K) (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K B.obj I) :
    ∃ (n : ℕ) (π : B →ₐc[K]
        MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))),
      Function.Surjective π ∧ ∀ b : B, π b = 0 ↔ b ∈ I.toIdeal := by
  apply exists_torusCoordinateMap B I
  exact ((TauCeti.HopfIdeal.isMaximalTorus_iff K B.obj I).mp hI).1

end ReductiveGroups
