import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusCoordinateMap
import OrbitComplexity.ReductiveGroups.Groups.Tangents.TangentImageIsomorphism
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalizableTangentImage

/-!
# Torus Quotient Tangent

Split coordinates of a fixed torus quotient preserve its tangent
image in the ambient affine group. -/

noncomputable section
namespace ReductiveGroups
open CategoryTheory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The split coordinate presentation has the fixed torus ideal as its kernel
and the same tangent image as the quotient map. -/
theorem exists_torusCoordinateMap_tangentImage
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K) (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.torusCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient B I)) :
    ∃ (n : ℕ) (π : B →ₐc[K]
        MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))),
      Function.Surjective π ∧
      (∀ b : B, π b = 0 ↔ b ∈ I.toIdeal) ∧
      diagonalizableTangentImage π =
        (TauCeti.derivationCompLieHom (B := K)
          (TauCeti.CommHopfAlgCat.mkQuotient B.obj I).hom).range := by
  obtain ⟨n, ⟨e⟩⟩ := torus_split_of_isAlgClosed
    (TauCeti.FiniteTypeCommHopfAlgCat.quotient B I) hI
  let eb := (forget₂ (TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K)
    (CommHopfAlgCat.{u} K)).mapIso e
  let f := CommHopfAlgCat.ofIso eb.symm
  let q := (TauCeti.CommHopfAlgCat.mkQuotient B.obj I).hom
  refine ⟨n, f.toBialgHom.comp q, ?_, ?_, ?_⟩
  · exact f.surjective.comp (TauCeti.CommHopfAlgCat.mkQuotient_surjective B.obj I)
  · intro b
    change f (q b) = 0 ↔ b ∈ I.toIdeal
    have hz : f (q b) = 0 ↔ q b = 0 :=
      ⟨fun h => f.injective (h.trans (map_zero f).symm), fun h => h ▸ map_zero f⟩
    exact hz.trans (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff B.obj I b)
  · exact tangentImage_comp_bialgEquiv q f

/-- The same statement for a fixed maximal torus. -/
theorem TorusQuotientTangent.exists_tangentImage
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K) (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K B.obj I) :
    ∃ (n : ℕ) (π : B →ₐc[K]
        MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))),
      Function.Surjective π ∧
      (∀ b : B, π b = 0 ↔ b ∈ I.toIdeal) ∧
      diagonalizableTangentImage π =
        (TauCeti.derivationCompLieHom (B := K)
          (TauCeti.CommHopfAlgCat.mkQuotient B.obj I).hom).range := by
  apply exists_torusCoordinateMap_tangentImage B I
  exact ((TauCeti.HopfIdeal.isMaximalTorus_iff K B.obj I).mp hI).1

end ReductiveGroups
