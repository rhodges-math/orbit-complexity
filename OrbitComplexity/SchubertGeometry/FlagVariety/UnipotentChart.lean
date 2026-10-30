import OrbitComplexity.GroupActions.Varieties.UnipotentVariety
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootCoordinateBasis
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootProductChartInverse
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.ProductPolynomialEquiv

/-!
# Root coordinates on the unipotent subgroup

An ordered product of root subgroups gives polynomial coordinates on the unipotent subgroup.
Positive-weight triangular inversion proves that these coordinates identify the coordinate
algebra with a polynomial algebra and give an affine-space isomorphism over the base field.

## Main definitions

* `SchubertGeometry.unipotentCoordinateEquiv`: the polynomial coordinate equivalence.
* `SchubertGeometry.unipotentChart`: the affine-space isomorphism over the field.
-/

namespace SchubertGeometry

noncomputable section

open ReductiveGroups TauCeti

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Ordered root products identify the unipotent coordinate algebra with a polynomial ring. -/
def unipotentCoordinateEquiv : G.unipotentAlgebra ≃ₐ[K]
    MvPolynomial (borelRootCharacterIndex G.borelIdeal G.torusSplit) K := by
  classical
  letI : Finite G.torusIndex := G.finiteIndex
  letI := finite_borelRootCharacterIndex G.borelIdeal G.torusSplit G.split_surjective
  letI := Fintype.ofFinite (borelRootCharacterIndex G.borelIdeal G.torusSplit)
  let hBasis := exists_borelRootCoordinateBasis
    G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive
  let x := Classical.choose hBasis
  let e := Classical.choose (Classical.choose_spec hBasis)
  have he := (Classical.choose_spec (Classical.choose_spec hBasis)).1
  have hx := (Classical.choose_spec (Classical.choose_spec hBasis)).2.1
  let l : List (borelRootCharacterIndex G.borelIdeal G.torusSplit) := Finset.univ.toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hall : ∀ j, j ∈ l := by intro j; simp [l]
  let hPoly := BorelRootProductPolynomialEquiv.exists_polynomialEquiv
    G.torusIdeal G.borelIdeal G.borel_le_torus G.isMaximalTorus G.isBorel
    G.torusSplit G.split_surjective G.split_eq_zero G.reductive x e he hx l hl hall
  let F := Classical.choose hPoly
  have hF := Classical.choose_spec hPoly
  exact borelRootProductQuotientChart G.borelIdeal G.isBorel G.torusSplit
    G.split_surjective x (fun i => he i ▸ (e i).property) l e F hF

open CategoryTheory AlgebraicGeometry

/-- Root coordinates give an affine-space chart on the entire unipotent subgroup. -/
def unipotentChart :
    (GroupActions.affineVariety K
      (MvPolynomial
        (Fin (Nat.card (borelRootCharacterIndex G.borelIdeal G.torusSplit))) K)).toOver ≅
        (GroupActions.unipotentVariety G).toOver := by
  letI := finite_borelRootCharacterIndex G.borelIdeal G.torusSplit G.split_surjective
  let e := (unipotentCoordinateEquiv G).trans
    (MvPolynomial.renameEquiv K (Finite.equivFin _))
  exact (algSpec (CommRingCat.of K)).mapIso (CommAlgCat.isoMk e).op

end

end SchubertGeometry
