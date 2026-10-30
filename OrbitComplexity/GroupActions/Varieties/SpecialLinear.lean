import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSl2Points
import OrbitComplexity.GroupActions.Varieties.AffineMorphisms
import OrbitComplexity.GroupActions.Varieties.AffineGroup
import OrbitComplexity.GroupActions.Varieties.ReductiveVariety
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth

/-! # Special linear varieties and simple-root morphisms -/

open CategoryTheory AlgebraicGeometry TauCeti
open scoped CategoryTheory.MonObj

noncomputable section

namespace GroupActions

universe u
variable (K : Type u) [Field K]

private theorem specialLinearReduced (n : ℕ) :
    IsReduced (SpecialLinear.coordinateHopfAlgebra K n) :=
  TauCeti.isReduced_of_smooth K (SpecialLinear.coordinateHopfAlgebra K n)

attribute [local instance] specialLinearReduced

/-- The special linear group as the affine variety of its coordinate Hopf algebra. -/
def specialLinearVariety (n : ℕ) : Variety K :=
  affineVariety K (SpecialLinear.coordinateHopfAlgebra K n)

/-- The coordinate Hopf algebra gives the special linear variety its group structure. -/
instance specialLinearVarietyGroup (n : ℕ) : GrpObj (specialLinearVariety K n).toOver :=
  affineVarietyGroup K (SpecialLinear.coordinateHopfAlgebra K n)

/-- Determinant-one matrices are the rational points of the special linear variety. -/
def specialLinearPointsMulEquiv (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) K ≃* (specialLinearVariety K n).points :=
  (SpecialLinear.pointsMulEquiv (R := K) (A := K) n).symm.trans
    (affineGroupPointsMulEquiv K (SpecialLinear.coordinateHopfAlgebra K n))

variable {K} (G : ReductiveGroups.ReductiveGroupData K)

private theorem reductiveReduced : IsReduced G.coordinateAlgebra := by
  let : Algebra.Smooth K G.coordinateAlgebra := G.reductive.smooth
  exact TauCeti.isReduced_of_smooth K G.coordinateAlgebra

attribute [local instance] reductiveReduced

variable [CharZero K] [IsAlgClosed K]

/-- The algebraic simple-root morphism from the special linear variety to the reductive group. -/
def simpleSl2Morphism (i : G.rootBase.support) :
    (specialLinearVariety K 2).toOver ⟶ (reductiveVariety G).toOver :=
  affineMorphism (G.simpleSl2Map i).toAlgHom

/-- The simple-root morphism preserves the algebraic group laws. -/
instance simpleSl2Morphism_isMonHom (i : G.rootBase.support) :
    IsMonHom (simpleSl2Morphism G i) := by
  change IsMonHom (((hopfSpec (CommRingCat.of K)).map
    (CommHopfAlgCat.ofHom (G.simpleSl2Map i)).op).hom.hom)
  infer_instance

/-- The algebraic simple-root morphism has the specified matrix-point homomorphism. -/
theorem simpleSl2Morphism_points (i : G.rootBase.support)
    (s : Matrix.SpecialLinearGroup (Fin 2) K) :
    Variety.mapPoints (simpleSl2Morphism G i) (specialLinearPointsMulEquiv K 2 s) =
      reductivePointsMulEquiv G (G.simpleSl2Points i s) := by
  let q := (SpecialLinear.pointsMulEquiv (R := K) (A := K) 2).symm s
  change Variety.mapPoints (affineMorphism (G.simpleSl2Map i).toAlgHom)
    (affinePointsEquiv q.ofConv) =
      affinePointsEquiv (q.ofConv.comp (G.simpleSl2Map i).toAlgHom)
  exact affineMorphism_points (G.simpleSl2Map i).toAlgHom q.ofConv

end GroupActions
