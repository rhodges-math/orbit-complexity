import OrbitComplexity.SchubertGeometry.Deodhar.PrefixLifts

/-! # Standard-form images of parameter lifts

The open parameter variety records the admissible raw tuples. Their ordered prefix
products give the point image of the regular group lift.
-/

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups BruhatIntervals
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private def parameterCoordinate (x : (deodharParameters G expression).points)
    (j : deodharIndex G expression) : K :=
  affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
    (Variety.mapPoints (deodharParameterInclusion G expression) x) j

private theorem selected_injective :
    Function.Injective (fun j : deodharIndex G expression => j.down.val) := by
  intro j k h
  apply ULift.ext
  exact Subtype.ext h

private def rawParameters (x : (deodharParameters G expression).points) :
    Fin word.length → K :=
  Function.extend (fun j : deodharIndex G expression => j.down.val)
    (parameterCoordinate G expression x) (fun _ => 0)

private theorem rawParameters_coord (x : (deodharParameters G expression).points)
    (j : deodharIndex G expression) :
    rawParameters G expression x j.down.val = parameterCoordinate G expression x j :=
  Function.Injective.extend_apply (selected_injective G expression) _ _ j

private theorem rawParameters_nonzero (x : (deodharParameters G expression).points)
    (j : Fin word.length) (hj : j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression) :
    rawParameters G expression x j ≠ 0 := by
  let i : deodharIndex G expression := ⟨⟨j, Or.inl hj⟩⟩
  change rawParameters G expression x i.down.val ≠ 0
  rw [rawParameters_coord]
  exact (deodharParameter_points G expression).subset ⟨x, rfl⟩ i hj

private theorem rawParameters_frame (n : ℕ) (x : (deodharParameters G expression).points) :
    Variety.mapPoints (deodharPrefixLift G expression n) x =
      reductivePointsEquiv G (deodharPrefix G expression
        (rawParameters G expression x) n) := by
  have hc : (fun j => parameterCoordinate G expression x ⟨j⟩) =
      (fun j => rawParameters G expression x j.val) :=
    funext (fun j => (rawParameters_coord G expression x ⟨j⟩).symm)
  have h := deodharPrefixLift_points G expression n x
  change _ = reductivePointsEquiv G (subwordRootProduct G expression
    (fun j => parameterCoordinate G expression x ⟨j⟩) n *
      subwordRepresentative G expression n) at h
  rw [hc] at h
  exact h.trans (congrArg (reductivePointsEquiv G)
    (deodharPrefix_rootProduct G expression (rawParameters G expression x) n).symm)

private theorem parameter_of_raw (n : ℕ) (p : Fin word.length → K)
    (hp : ∀ j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression, p j ≠ 0) :
    ∃ x : (deodharParameters G expression).points,
      Variety.mapPoints (deodharPrefixLift G expression n) x =
        reductivePointsEquiv G (deodharPrefix G expression p n) := by
  let a : deodharIndex G expression → K := fun j => p j.down.val
  let q := (affineSpaceVarietyPointsEquiv K (deodharIndex G expression)).symm a
  have hq : q ∈ Set.range (Variety.mapPoints (deodharParameterInclusion G expression)) := by
    apply (deodharParameter_points G expression).symm.subset
    intro j hj
    change affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
      ((affineSpaceVarietyPointsEquiv K (deodharIndex G expression)).symm a) j ≠ 0
    rw [Equiv.apply_symm_apply]
    exact hp j.down.val hj
  obtain ⟨x, hx⟩ := hq
  have hcoords (j : deodharIndex G expression) :
      parameterCoordinate G expression x j = p j.down.val := by
    exact (congrArg (fun z : (affineSpaceVariety K (deodharIndex G expression)).points =>
      affineSpaceVarietyPointsEquiv K (deodharIndex G expression) z j) hx).trans
        (congrFun (Equiv.apply_symm_apply
          (affineSpaceVarietyPointsEquiv K (deodharIndex G expression)) a) j)
  have hc : (fun j => parameterCoordinate G expression x ⟨j⟩) = (fun j => p j.val) :=
    funext (fun j => hcoords ⟨j⟩)
  have h := deodharPrefixLift_points G expression n x
  change _ = reductivePointsEquiv G (subwordRootProduct G expression
    (fun j => parameterCoordinate G expression x ⟨j⟩) n *
      subwordRepresentative G expression n) at h
  rw [hc] at h
  exact ⟨x, h.trans (congrArg (reductivePointsEquiv G)
    (deodharPrefix_rootProduct G expression p n).symm)⟩

/-- The prefix-lift point image consists of raw products with nonzero omitted coordinates. -/
theorem deodharPrefixLift_image (n : ℕ) :
    Set.range (fun x : (deodharParameters G expression).points =>
      (reductivePointsEquiv G).symm (Variety.mapPoints
        (deodharPrefixLift G expression n) x)) =
      {g | ∃ p : Fin word.length → K,
        (∀ j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression, p j ≠ 0) ∧
          deodharPrefix G expression p n = g} := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨rawParameters G expression x, fun j hj =>
      rawParameters_nonzero G expression x j hj, ?_⟩
    apply (reductivePointsEquiv G).injective
    rw [Equiv.apply_symm_apply]
    exact (rawParameters_frame G expression n x).symm
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨x, hx⟩ := parameter_of_raw G expression n p hp
    refine ⟨x, ?_⟩
    exact (congrArg (reductivePointsEquiv G).symm hx).trans
      (Equiv.symm_apply_apply (reductivePointsEquiv G) _)
end
end SchubertGeometry
