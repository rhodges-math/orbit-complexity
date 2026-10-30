import OrbitComplexity.SchubertGeometry.FlagVariety.BigCell
import OrbitComplexity.GroupActions.Varieties.OppositeUnipotentPoints
import OrbitComplexity.GroupActions.Varieties.BorelPoints

/-!
# Rational points and projections of the big cell

The affine product description supplies its two scheme projections. On rational points,
the big-cell open immersion multiplies the corresponding opposite-unipotent and Borel points.

## Main definitions

* `SchubertGeometry.bigCellFst`: the opposite unipotent projection.
* `SchubertGeometry.bigCellSnd`: the Borel projection.
* `SchubertGeometry.bigCellPointsEquiv`: rational points as pairs of subgroup points.

## Main results

* `SchubertGeometry.bigCellMorphism_points`: compatibility with subgroup multiplication.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace SchubertGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The first projection of the affine big cell is its opposite unipotent coordinate. -/
def bigCellFst : (bigCellVariety G).toOver ⟶ (GroupActions.oppositeUnipotentVariety G).toOver :=
  (algSpec (CommRingCat.of K)).map
    (CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft :
      G.oppositeUnipotentAlgebra →ₐ[K] G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra)).op

/-- The second projection of the affine big cell is its Borel coordinate. -/
def bigCellSnd : (bigCellVariety G).toOver ⟶ (GroupActions.borelVariety G).toOver :=
  (algSpec (CommRingCat.of K)).map
    (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight :
      G.borelAlgebra →ₐ[K] G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra)).op

/-- Rational points of the big cell are pairs of subgroup rational points. -/
def bigCellPointsEquiv : (bigCellVariety G).points ≃
    (GroupActions.oppositeUnipotentVariety G).points × (GroupActions.borelVariety G).points :=
  GroupActions.affineProductPointsEquiv K G.oppositeUnipotentAlgebra G.borelAlgebra

/-- The first component of the point equivalence is induced by the first scheme projection. -/
theorem bigCellPointsEquiv_fst (x : (bigCellVariety G).points) :
    (bigCellPointsEquiv G x).1 = GroupActions.Variety.mapPoints (bigCellFst G) x := by
  apply Subtype.ext
  exact GroupActions.affineProductPointsEquiv_fst K
    G.oppositeUnipotentAlgebra G.borelAlgebra x

/-- The second component of the point equivalence is induced by the second scheme projection. -/
theorem bigCellPointsEquiv_snd (x : (bigCellVariety G).points) :
    (bigCellPointsEquiv G x).2 = GroupActions.Variety.mapPoints (bigCellSnd G) x := by
  apply Subtype.ext
  exact GroupActions.affineProductPointsEquiv_snd K
    G.oppositeUnipotentAlgebra G.borelAlgebra x

/-- Big-cell multiplication on rational points is the product of the two subgroup points. -/
theorem bigCellMorphism_points (x : (bigCellVariety G).points) :
    GroupActions.Variety.mapPoints (bigCellMorphism G) x =
      GroupActions.reductivePointsEquiv G
        ((GroupActions.oppositeUnipotentPointsMulEquiv G (bigCellPointsEquiv G x).1 : G.points) *
          (GroupActions.borelPointsMulEquiv G (bigCellPointsEquiv G x).2 : G.points)) := by
  let e : (G.oppositeUnipotentAlgebra ⊗[K] G.borelAlgebra →ₐ[K] K) ≃
      (bigCellVariety G).points := GroupActions.affinePointsEquiv
  obtain ⟨q, rfl⟩ := e.surjective x
  let p := GroupActions.tensorAlgebraPointsEquiv K
    G.oppositeUnipotentAlgebra G.borelAlgebra q
  let eA : (G.oppositeUnipotentAlgebra →ₐ[K] K) ≃
      (GroupActions.oppositeUnipotentVariety G).points := GroupActions.affinePointsEquiv
  let eB : (G.borelAlgebra →ₐ[K] K) ≃
      (GroupActions.borelVariety G).points := GroupActions.affinePointsEquiv
  let qI : G.coordinateAlgebra →ₐ[K] G.oppositeUnipotentAlgebra :=
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeUnipotentIdeal).hom.toAlgHom
  let qJ : G.coordinateAlgebra →ₐ[K] G.borelAlgebra :=
    (TauCeti.CommHopfAlgCat.mkQuotient
      (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal).hom.toAlgHom
  have hpair : bigCellPointsEquiv G (e q) =
      (eA p.1, eB p.2) := by
    change GroupActions.affineProductPointsEquiv K
      G.oppositeUnipotentAlgebra G.borelAlgebra (GroupActions.affinePointsEquiv q) = _
    simp only [GroupActions.affineProductPointsEquiv, Equiv.trans_apply,
      Equiv.symm_apply_apply, Equiv.prodCongr_apply]
    rfl
  have hA : (GroupActions.oppositeUnipotentPointsMulEquiv G (eA p.1) : G.points) =
      WithConv.toConv (p.1.comp qI) := by
    rw [GroupActions.oppositeUnipotentPointsMulEquiv_coe]
    change TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.oppositeUnipotentIdeal (CommAlgCat.of K K)
        (WithConv.toConv (eA.symm (eA p.1))) = _
    rw [eA.symm_apply_apply]
    rfl
  have hB : (GroupActions.borelPointsMulEquiv G (eB p.2) : G.points) =
      WithConv.toConv (p.2.comp qJ) := by
    rw [GroupActions.borelPointsMulEquiv_coe]
    change TauCeti.CommHopfAlgCat.quotientPointsHom
        (CommHopfAlgCat.of K G.coordinateAlgebra) G.borelIdeal (CommAlgCat.of K K)
        (WithConv.toConv (eB.symm (eB p.2))) = _
    rw [eB.symm_apply_apply]
    rfl
  rw [hpair, hA, hB]
  apply Subtype.ext
  rw [GroupActions.reductivePointsEquiv_apply]
  change Spec.map (CommRingCat.ofHom q.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (bigCellCoordinate G).toRingHom) =
    Spec.map (CommRingCat.ofHom
      ((WithConv.toConv (p.1.comp qI) * WithConv.toConv (p.2.comp qJ)).ofConv).toRingHom)
  rw [← Spec.map_comp]
  have hq := GroupActions.affineMulMap_points qI qJ p
  change ((GroupActions.tensorAlgebraPointsEquiv K
    G.oppositeUnipotentAlgebra G.borelAlgebra).symm
      ((GroupActions.tensorAlgebraPointsEquiv K
        G.oppositeUnipotentAlgebra G.borelAlgebra) q)).comp
          (GroupActions.affineMulMap qI qJ) = _ at hq
  rw [Equiv.symm_apply_apply] at hq
  exact congrArg (fun φ : G.coordinateAlgebra →ₐ[K] K =>
    Spec.map (CommRingCat.ofHom φ.toRingHom)) hq

end

end SchubertGeometry
