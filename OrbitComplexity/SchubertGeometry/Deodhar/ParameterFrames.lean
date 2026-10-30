import OrbitComplexity.SchubertGeometry.Deodhar.PrefixLifts
import OrbitComplexity.SchubertGeometry.Deodhar.PrefixProducts
import OrbitComplexity.SchubertGeometry.Deodhar.ParameterSelectedPoints
import OrbitComplexity.SchubertGeometry.Deodhar.ParameterStepPoints

/-! # Group frames for parameter steps

A prefix parameter point determines one raw parameter tuple on the full word.
At each step, the two adjacent regular group lifts use the corresponding ordered products,
and a selected new coordinate gives the parameter at the appended word position.
-/

open CategoryTheory BruhatIntervals ReductiveGroups GroupActions GroupActions.Variety
open SchubertGeometry
open CartesianMonoidalCategory MonoidalCategory
attribute [local irreducible] SchubertGeometry.deodharPositiveStepIso
  SchubertGeometry.deodharNegativeStepIso SchubertGeometry.deodharEqualStepIso
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private theorem frame_of_coordinates (n : ℕ)
    (a : deodharIndex G (expression.take n) → K) (p : Fin word.length → K)
    (ha : ∀ j : deodharIndex G (expression.take n),
      a j = p (Subexpression.takePosition n j.down.val)) :
    subwordRootProduct G (expression.take n) (fun j => a ⟨j⟩) n *
        subwordRepresentative G (expression.take n) n =
      deodharPrefix G expression p n := by
  have hc : (fun j => a ⟨j⟩) = (fun j => p (Subexpression.takePosition n j.val)) :=
    funext (fun j => ha ⟨j⟩)
  have hroot := congrArg (fun q => subwordRootProduct G (expression.take n) q n *
    subwordRepresentative G (expression.take n) n) hc
  have hprod := deodharPrefix_rootProduct G (expression.take n)
    (fun j => p (Subexpression.takePosition n j)) n
  have ht := (deodharPrefix_take G expression p n n).trans
    (congrArg (deodharPrefix G expression p) (Nat.min_self n))
  exact hroot.trans (hprod.symm.trans ht)

private theorem take_index_injective (n : ℕ) :
    Function.Injective (fun j : deodharIndex G (expression.take n) =>
      (deodharTakeIndex G expression n j).down.val) := by
  intro j k h
  apply ULift.ext
  apply Subtype.ext
  apply Fin.ext
  exact congrArg (fun a : Fin word.length => a.val) h

private def prefixParameters (n : ℕ)
    (x : (deodharParameters G (expression.take n)).points) : Fin word.length → K :=
  Function.extend (fun j : deodharIndex G (expression.take n) =>
    (deodharTakeIndex G expression n j).down.val)
    (affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n))
      (mapPoints (deodharParameterInclusion G (expression.take n)) x)) (fun _ => 0)

private theorem prefixParameters_coord (n : ℕ)
    (x : (deodharParameters G (expression.take n)).points)
    (j : deodharIndex G (expression.take n)) :
    prefixParameters G expression n x (Subexpression.takePosition n j.down.val) =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n))
        (mapPoints (deodharParameterInclusion G (expression.take n)) x) j :=
  Function.Injective.extend_apply (take_index_injective G expression n) _ _ j

private theorem prefixLift_frame (n : ℕ)
    (x : (deodharParameters G (expression.take n)).points) :
    mapPoints (deodharPrefixLift G (expression.take n) n) x =
      reductivePointsEquiv G
        (deodharPrefix G expression (prefixParameters G expression n x) n) := by
  have hp := frame_of_coordinates G expression n
    (affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n))
      (mapPoints (deodharParameterInclusion G (expression.take n)) x))
    (prefixParameters G expression n x)
    (fun j => (prefixParameters_coord G expression n x j).symm)
  exact (deodharPrefixLift_points G (expression.take n) n x).trans
    (congrArg (fun g : G.points => reductivePointsEquiv G g) hp)

private theorem previous_frame (n : Fin word.length)
    (l : deodharIndex G (expression.take n.val) →
      deodharIndex G (expression.take (n.val + 1)))
    (he : ∀ j, (l j).down.val.val = j.down.val.val)
    (b : (deodharParameters G (expression.take (n.val + 1))).toOver ⟶
      (deodharParameters G (expression.take n.val)).toOver)
    (x : (deodharParameters G (expression.take (n.val + 1))).points)
    (hc : ∀ j : deodharIndex G (expression.take n.val),
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
        (mapPoints (deodharParameterInclusion G (expression.take n.val))
          (mapPoints b x)) j =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (mapPoints (deodharParameterInclusion G (expression.take (n.val + 1))) x)
        (l j)) :
    mapPoints (b ≫ deodharPrefixLift G (expression.take n.val) n.val) x =
      reductivePointsEquiv G (deodharPrefix G expression
        (prefixParameters G expression (n.val + 1) x) n.val) := by
  have hcoeff : ∀ j : deodharIndex G (expression.take n.val),
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
        (mapPoints (deodharParameterInclusion G (expression.take n.val))
          (mapPoints b x)) j =
      prefixParameters G expression (n.val + 1) x
        (Subexpression.takePosition n.val j.down.val) := by
    intro j
    have hi : Subexpression.takePosition (n.val + 1) (l j).down.val =
        Subexpression.takePosition n.val j.down.val := Fin.ext (he j)
    exact (hc j).trans
      ((prefixParameters_coord G expression (n.val + 1) x (l j)).symm.trans
        (congrArg (prefixParameters G expression (n.val + 1) x) hi))
  have hframe := frame_of_coordinates G expression n.val
    (affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
      (mapPoints (deodharParameterInclusion G (expression.take n.val)) (mapPoints b x)))
    (prefixParameters G expression (n.val + 1) x) hcoeff
  exact (mapPoints_comp (X := deodharParameters G (expression.take (n.val + 1)))
    (Y := deodharParameters G (expression.take n.val)) (Z := reductiveVariety G)
    b (deodharPrefixLift G (expression.take n.val) n.val) x).trans
      ((deodharPrefixLift_points G (expression.take n.val) n.val (mapPoints b x)).trans
        (congrArg (fun g : G.points => reductivePointsEquiv G g) hframe))

private theorem last_parameter (n : Fin word.length)
    (e : deodharIndex G (expression.take (n.val + 1)) ≃
      deodharIndex G (expression.take n.val) ⊕ PUnit.{u+1})
    (he : (e.symm (Sum.inr PUnit.unit)).down.val.val = n.val)
    (x : (deodharParameters G (expression.take (n.val + 1))).points) :
    prefixParameters G expression (n.val + 1) x n =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (mapPoints (deodharParameterInclusion G (expression.take (n.val + 1))) x)
        (e.symm (Sum.inr PUnit.unit)) := by
  have hi : Subexpression.takePosition (n.val + 1) (e.symm (Sum.inr PUnit.unit)).down.val =
      n := Fin.ext he
  exact (congrArg (prefixParameters G expression (n.val + 1) x) hi.symm).trans
    (prefixParameters_coord G expression (n.val + 1) x (e.symm (Sum.inr PUnit.unit)))

private theorem positiveStep_frame (n : Fin word.length)
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points) :
    mapPoints ((deodharPositiveStepIso G expression n hn).hom ≫
      deodharPrefixLift G (expression.take n.val) n.val) x =
      reductivePointsEquiv G (deodharPrefix G expression
        (prefixParameters G expression (n.val + 1) x) n.val) :=
  previous_frame G expression n (deodharStepIndexPositive G expression n hn).symm
    (deodharStepIndexPositive_val G expression n hn)
    (deodharPositiveStepIso G expression n hn).hom x
    (deodharPositiveStep_coord G expression n hn x)

private theorem negativeStep_frame (n : Fin word.length)
    (hn : n ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points) :
    mapPoints (((deodharNegativeStepIso G expression n hn).hom ≫
      fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver) ≫
        deodharPrefixLift G (expression.take n.val) n.val) x =
      reductivePointsEquiv G (deodharPrefix G expression
        (prefixParameters G expression (n.val + 1) x) n.val) := by
  let b : (deodharParameters G (expression.take (n.val + 1))).toOver ⟶
      (deodharParameters G (expression.take n.val)).toOver :=
    (deodharNegativeStepIso G expression n hn).hom ≫
      fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver
  apply previous_frame G expression n
    (fun j => (deodharStepIndexSelected G expression n (Or.inr hn)).symm (Sum.inl j))
    (deodharStepIndexSelected_val G expression n (Or.inr hn)).1 b x
  intro j
  have hp := mapPoints_comp (X := deodharParameters G (expression.take (n.val + 1)))
    (Y := deodharParameters G (expression.take n.val))
    (Z := affineSpaceVariety K (deodharIndex G (expression.take n.val)))
    b (deodharParameterInclusion G (expression.take n.val)) x
  exact (congrArg (fun z : (affineSpaceVariety K
    (deodharIndex G (expression.take n.val))).points =>
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val)) z j) hp).symm.trans
        (deodharNegativeStep_coord G expression n hn x j)

private theorem equalStep_frame (n : Fin word.length)
    (hn : n ∈ equalSteps (weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points) :
    mapPoints (((deodharEqualStepIso G expression n hn).hom ≫
      fst (deodharParameters G (expression.take n.val)).toOver
        ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver) ≫
          deodharPrefixLift G (expression.take n.val) n.val) x =
      reductivePointsEquiv G (deodharPrefix G expression
        (prefixParameters G expression (n.val + 1) x) n.val) := by
  let b : (deodharParameters G (expression.take (n.val + 1))).toOver ⟶
      (deodharParameters G (expression.take n.val)).toOver :=
    (deodharEqualStepIso G expression n hn).hom ≫
      fst (deodharParameters G (expression.take n.val)).toOver
        ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver
  apply previous_frame G expression n
    (fun j => (deodharStepIndexSelected G expression n (Or.inl hn)).symm (Sum.inl j))
    (deodharStepIndexSelected_val G expression n (Or.inl hn)).1 b x
  intro j
  have hp := mapPoints_comp (X := deodharParameters G (expression.take (n.val + 1)))
    (Y := deodharParameters G (expression.take n.val))
    (Z := affineSpaceVariety K (deodharIndex G (expression.take n.val)))
    b (deodharParameterInclusion G (expression.take n.val)) x
  exact (congrArg (fun z : (affineSpaceVariety K
    (deodharIndex G (expression.take n.val))).points =>
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val)) z j) hp).symm.trans
        (deodharEqualStep_coord G expression n hn x j)

/-- A regular parameter-prefix lift is the ordered Deodhar product of a full parameter tuple. -/
theorem exists_deodharPrefix_frame (n : ℕ)
    (x : (deodharParameters G (expression.take n)).points) :
    ∃ p : Fin word.length → K,
      mapPoints (deodharPrefixLift G (expression.take n) n) x =
        reductivePointsEquiv G (deodharPrefix G expression p n) :=
  ⟨prefixParameters G expression n x, prefixLift_frame G expression n x⟩

/-- An increasing step uses one raw parameter tuple for its two adjacent prefix lifts. -/
theorem deodharPositiveStep_frames (n : Fin word.length)
    (hn : n ∈ positiveSteps (weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points) :
    ∃ p : Fin word.length → K,
      mapPoints (deodharPrefixLift G (expression.take (n.val + 1)) (n.val + 1)) x =
        reductivePointsEquiv G (deodharPrefix G expression p (n.val + 1)) ∧
      mapPoints ((deodharPositiveStepIso G expression n hn).hom ≫
        deodharPrefixLift G (expression.take n.val) n.val) x =
          reductivePointsEquiv G (deodharPrefix G expression p n.val) :=
  ⟨prefixParameters G expression (n.val + 1) x,
    prefixLift_frame G expression (n.val + 1) x, positiveStep_frame G expression n hn x⟩

/-- A decreasing step shares the preceding raw frame and reads its new additive parameter. -/
theorem deodharNegativeStep_frames (n : Fin word.length)
    (hn : n ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points) :
    ∃ p : Fin word.length → K,
      mapPoints (deodharPrefixLift G (expression.take (n.val + 1)) (n.val + 1)) x =
        reductivePointsEquiv G (deodharPrefix G expression p (n.val + 1)) ∧
      mapPoints (((deodharNegativeStepIso G expression n hn).hom ≫
        fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver) ≫
          deodharPrefixLift G (expression.take n.val) n.val) x =
        reductivePointsEquiv G (deodharPrefix G expression p n.val) ∧
      p n = (additivePointsEquiv K).symm (mapPoints
        ((deodharNegativeStepIso G expression n hn).hom ≫
          snd (deodharParameters G (expression.take n.val)).toOver
            (additiveVariety K).toOver) x) := by
  refine ⟨prefixParameters G expression (n.val + 1) x,
    prefixLift_frame G expression (n.val + 1) x, negativeStep_frame G expression n hn x, ?_⟩
  exact (last_parameter G expression n
    (deodharStepIndexSelected G expression n (Or.inr hn))
    (deodharStepIndexSelected_val G expression n (Or.inr hn)).2 x).trans
      (deodharNegativeStep_last G expression n hn x).symm

/-- An omitted step shares the preceding raw frame and reads its nonzero parameter. -/
theorem deodharEqualStep_frames (n : Fin word.length)
    (hn : n ∈ equalSteps (weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points) :
    ∃ p : Fin word.length → K,
      mapPoints (deodharPrefixLift G (expression.take (n.val + 1)) (n.val + 1)) x =
        reductivePointsEquiv G (deodharPrefix G expression p (n.val + 1)) ∧
      mapPoints (((deodharEqualStepIso G expression n hn).hom ≫
        fst (deodharParameters G (expression.take n.val)).toOver
          ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver) ≫
            deodharPrefixLift G (expression.take n.val) n.val) x =
        reductivePointsEquiv G (deodharPrefix G expression p n.val) ∧
      p n = (additivePointsEquiv K).symm (mapPoints
        ((deodharEqualStepIso G expression n hn).hom ≫
          snd (deodharParameters G (expression.take n.val)).toOver
            ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver ≫
              (additiveVariety K).openInclusion (additiveNonzero K)) x) := by
  refine ⟨prefixParameters G expression (n.val + 1) x,
    prefixLift_frame G expression (n.val + 1) x, equalStep_frame G expression n hn x, ?_⟩
  exact (last_parameter G expression n
    (deodharStepIndexSelected G expression n (Or.inl hn))
    (deodharStepIndexSelected_val G expression n (Or.inl hn)).2 x).trans
      (deodharEqualStep_last G expression n hn x).symm

end
end SchubertGeometry
