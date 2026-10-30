import OrbitComplexity.SchubertGeometry.FlagVariety.Quotient
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-! # Openness of the flag quotient

On each translated big cell the quotient is the open affine product projection.
-/

open CategoryTheory AlgebraicGeometry Topology
open scoped TensorProduct

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem bigCellFstOpen : IsOpenMap (bigCellFst G).left := by
  change IsOpenMap (PrimeSpectrum.comap
    (algebraMap G.oppositeUnipotentAlgebra (G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra)))
  exact PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field

/-- The quotient morphism is open on the underlying scheme spaces. -/
theorem flagQuotient_isOpenMap : IsOpenMap (flagQuotient G) := by
  intro U hU
  have he : flagQuotient G '' U = ⋃ g : G.points,
      bigCellFlagChart G g '' ((translatedBigCell G g).left ⁻¹' U) := by
    apply Set.Subset.antisymm
    · rintro y ⟨a, ha, hay⟩
      obtain ⟨g, x, hx⟩ := (bigCellCover G).exists_eq a
      change G.points at g
      change (bigCellVariety G).scheme at x
      change (translatedBigCell G g).left x = a at hx
      refine Set.mem_iUnion.mpr ⟨g, x, ?_, ?_⟩
      · change (translatedBigCell G g).left x ∈ U
        rw [hx]
        exact ha
      have hq := congrArg (fun f : (bigCellVariety G).scheme ⟶ flagScheme G => f x)
        (translatedBigCell_quotient G g)
      exact hq.symm.trans ((congrArg (flagQuotient G) hx).trans hay)
    · intro y hy
      obtain ⟨g, x, hx, hxy⟩ := Set.mem_iUnion.mp hy
      refine ⟨(translatedBigCell G g).left x, hx, ?_⟩
      have hq := congrArg (fun f : (bigCellVariety G).scheme ⟶ flagScheme G => f x)
        (translatedBigCell_quotient G g)
      exact hq.trans hxy
  rw [he]
  apply isOpen_iUnion
  intro g
  exact ((flagSchemeChart G g).isOpenEmbedding.isOpenMap.comp (bigCellFstOpen G)) _
    (hU.preimage (translatedBigCell G g).left.continuous)

end
end SchubertGeometry