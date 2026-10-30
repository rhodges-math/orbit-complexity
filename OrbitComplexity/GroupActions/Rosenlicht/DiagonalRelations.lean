import OrbitComplexity.GroupActions.Rosenlicht.RelationChartLifts
import OrbitComplexity.GroupActions.Rosenlicht.RelationDiagonal
import OrbitComplexity.GroupActions.Rosenlicht.RelationPointEquations

/-!
# DiagonalRelations
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The diagonal pair of rational points annihilates the regular relation ideal
on every pair of affine charts containing that point. -/
theorem relationChart_diagonal_relations (U V : X.scheme.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) {ι : Type v}
    (c : ι → Γ(X.scheme, V))
    (p : (X.openSubvariety U).points) (q : (X.openSubvariety V).points)
    (he : mapPoints (X.openInclusion U) p = mapPoints (X.openInclusion V) q) :
    letI := relationChartAlgebra H X U V
    RingHom.ker (relationChartCoordinates H X U V c) ≤
      RingHom.ker (MvPolynomial.eval₂Hom (affineOpenPointEval X U hU p)
        (fun a ↦ affineOpenPointEval X V hV q (c a))) := by
  let x := mapPoints (X.openInclusion U) p
  let r := (relationDiagonalPoint H X x).val
  have hfirst : r ≫ (orbitRelationProjection H X).left = p.val ≫ U.ι := by
    exact congrArg Subtype.val (relationDiagonalPoint_first H X x)
  have hsecond : r ≫ (orbitRelationSecond H X).left = q.val ≫ V.ι := by
    exact congrArg Subtype.val ((relationDiagonalPoint_second H X x).trans he)
  obtain ⟨t, ht, hs⟩ := relationChartPoint_of_pair H X U V p q r hfirst hsecond
  exact relationChartPoint_relations H X U V hU hV c p q t ht hs

end

end GroupActions.Variety
