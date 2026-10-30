import OrbitComplexity.SchubertGeometry.Deodhar.ParameterSelectedCoordinates

/-! # Selected-step prefix projection

The product decompositions at decreasing and omitted steps commute with the morphisms
that forget parameters after an initial subword.
-/

open CategoryTheory AlgebraicGeometry GroupActions BruhatIntervals
open CartesianMonoidalCategory MonoidalCategory
attribute [local irreducible] SchubertGeometry.deodharNegativeStepIso
  SchubertGeometry.deodharEqualStepIso
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private theorem selectedProjection (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∨
      n ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (f : (deodharParameters G (expression.take (n.val + 1))).toOver ⟶
      (deodharParameters G (expression.take n.val)).toOver)
    (hf : ∀ (x : (deodharParameters G (expression.take (n.val + 1))).points)
      (j : deodharIndex G (expression.take n.val)),
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
        (Variety.mapPoints (X := deodharParameters G (expression.take n.val))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take n.val)))
          (deodharParameterInclusion G (expression.take n.val))
          (Variety.mapPoints (X := deodharParameters G (expression.take (n.val + 1)))
            (Y := deodharParameters G (expression.take n.val)) f x)) j =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (Variety.mapPoints (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take (n.val + 1))))
          (deodharParameterInclusion G (expression.take (n.val + 1))) x)
        ((deodharStepIndexSelected G expression n hn).symm (Sum.inl j))) :
    deodharParameterProjection G expression (n.val + 1) ≫ f =
      deodharParameterProjection G expression n.val := by
  apply Variety.mapPoints_injective (X := deodharParameters G expression)
    (Y := deodharParameters G (expression.take n.val))
  funext x
  apply Variety.mapPoints_injective_of_mono
    (X := deodharParameters G (expression.take n.val))
    (Y := affineSpaceVariety K (deodharIndex G (expression.take n.val)))
    (deodharParameterInclusion G (expression.take n.val))
  apply (affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))).injective
  funext j
  have hp := Variety.mapPoints_comp (X := deodharParameters G expression)
    (Y := deodharParameters G (expression.take (n.val + 1)))
    (Z := deodharParameters G (expression.take n.val))
    (deodharParameterProjection G expression (n.val + 1)) f x
  have hc := hf (Variety.mapPoints (X := deodharParameters G expression)
    (Y := deodharParameters G (expression.take (n.val + 1)))
    (deodharParameterProjection G expression (n.val + 1)) x) j
  have hnew := deodharParameterProjection_coord G expression (n.val + 1) x
    ((deodharStepIndexSelected G expression n hn).symm (Sum.inl j))
  have hold := deodharParameterProjection_coord G expression n.val x j
  have hi : deodharTakeIndex G expression (n.val + 1)
      ((deodharStepIndexSelected G expression n hn).symm (Sum.inl j)) =
      deodharTakeIndex G expression n.val j := by
    apply ULift.ext
    apply Subtype.ext
    apply Fin.ext
    exact (deodharStepIndexSelected_val G expression n hn).1 j
  have hcoord := congrArg (fun k => affineSpaceVarietyPointsEquiv K
    (deodharIndex G expression)
      (Variety.mapPoints (X := deodharParameters G expression)
        (Y := affineSpaceVariety K (deodharIndex G expression))
        (deodharParameterInclusion G expression) x) k) hi
  exact (congrArg (fun y : (deodharParameters G (expression.take n.val)).points =>
    affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
      (Variety.mapPoints (X := deodharParameters G (expression.take n.val))
        (Y := affineSpaceVariety K (deodharIndex G (expression.take n.val)))
        (deodharParameterInclusion G (expression.take n.val)) y) j) hp).trans
          (hc.trans (hnew.trans (hcoord.trans hold.symm)))

/-- Decreasing-step decomposition commutes with projection from the full parameters. -/
theorem deodharNegativeStep_projection (n : Fin word.length)
    (hn : n ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    deodharParameterProjection G expression (n.val + 1) ≫
        (deodharNegativeStepIso G expression n hn).hom ≫
        fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver =
      deodharParameterProjection G expression n.val := by
  apply selectedProjection G expression n (Or.inr hn)
  intro x j
  let C := deodharParameters G (expression.take (n.val + 1))
  let A := deodharParameters G (expression.take n.val)
  let Q := affineSpaceVariety K (deodharIndex G (expression.take n.val))
  let f : C.toOver ⟶ A.toOver :=
    (deodharNegativeStepIso G expression n hn).hom ≫ fst A.toOver (additiveVariety K).toOver
  let i := deodharParameterInclusion G (expression.take n.val)
  have he := Variety.mapPoints_comp (X := C) (Y := A) (Z := Q) f i x
  have ha : f ≫ i = (deodharNegativeStepIso G expression n hn).hom ≫
      fst A.toOver (additiveVariety K).toOver ≫ i :=
    Category.assoc _ _ _
  have hh := congrArg (fun g : C.toOver ⟶ Q.toOver =>
    affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
      (Variety.mapPoints (X := C) (Y := Q) g x) j) ha
  exact (congrArg (fun y : Q.points => affineSpaceVarietyPointsEquiv K
    (deodharIndex G (expression.take n.val)) y j) he).symm.trans
      (hh.trans (deodharNegativeStep_coord G expression n hn x j))

/-- Omitted-step decomposition commutes with projection from the full parameters. -/
theorem deodharEqualStep_projection (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    deodharParameterProjection G expression (n.val + 1) ≫
        (deodharEqualStepIso G expression n hn).hom ≫
        fst (deodharParameters G (expression.take n.val)).toOver
          ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver =
      deodharParameterProjection G expression n.val := by
  apply selectedProjection G expression n (Or.inl hn)
  intro x j
  let C := deodharParameters G (expression.take (n.val + 1))
  let A := deodharParameters G (expression.take n.val)
  let B := (additiveVariety K).openSubvariety (additiveNonzero K)
  let Q := affineSpaceVariety K (deodharIndex G (expression.take n.val))
  let f : C.toOver ⟶ A.toOver :=
    (deodharEqualStepIso G expression n hn).hom ≫ fst A.toOver B.toOver
  let i := deodharParameterInclusion G (expression.take n.val)
  have he := Variety.mapPoints_comp (X := C) (Y := A) (Z := Q) f i x
  have ha : f ≫ i = (deodharEqualStepIso G expression n hn).hom ≫
      fst A.toOver B.toOver ≫ i := Category.assoc _ _ _
  have hh := congrArg (fun g : C.toOver ⟶ Q.toOver =>
    affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
      (Variety.mapPoints (X := C) (Y := Q) g x) j) ha
  exact (congrArg (fun y : Q.points => affineSpaceVarietyPointsEquiv K
    (deodharIndex G (expression.take n.val)) y j) he).symm.trans
      (hh.trans (deodharEqualStep_coord G expression n hn x j))

end SchubertGeometry
