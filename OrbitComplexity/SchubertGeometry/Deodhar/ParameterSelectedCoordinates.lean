import OrbitComplexity.SchubertGeometry.Deodhar.ParameterSteps

/-! # Selected-step parameter coordinates

Decreasing and omitted steps retain the old coordinates and read the appended coordinate
as the additive parameter in the product identification.
-/

open CategoryTheory AlgebraicGeometry GroupActions BruhatIntervals
open CartesianMonoidalCategory MonoidalCategory
attribute [local irreducible] SchubertGeometry.deodharNegativeStepIso
  SchubertGeometry.deodharEqualStepIso GroupActions.coordinateStepIso
  GroupActions.coordinateUnitStepIso GroupActions.coordinateReindexIso
noncomputable section
namespace SchubertGeometry
universe u

private theorem appendedStep_points {K : Type u} [Field K] [IsAlgClosed K]
    {ι κ : Type u} [Finite ι] [Finite κ] (e : ι ≃ κ ⊕ PUnit.{u+1})
    (S : Finset ι) (T : Finset κ) (h : S.map e.toEmbedding = coordinateStepInl T)
    (x : ((affineSpaceVariety K ι).openSubvariety (coordinateOpen K S)).points) :
    let A := (affineSpaceVariety K κ).openSubvariety (coordinateOpen K T)
    let r := coordinateReindexIso K e S (coordinateStepInl T) h
    let c := coordinateStepIso K T
    ((∀ j : κ, affineSpaceVarietyPointsEquiv K κ
      (Variety.mapPoints (r.hom ≫ c.hom ≫ fst A.toOver (additiveVariety K).toOver ≫
        (affineSpaceVariety K κ).openInclusion (coordinateOpen K T)) x) j =
      affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints
        ((affineSpaceVariety K ι).openInclusion (coordinateOpen K S)) x) (e.symm (Sum.inl j))) ∧
    ((additivePointsEquiv K).symm (Variety.mapPoints
      (r.hom ≫ c.hom ≫ snd A.toOver (additiveVariety K).toOver) x) =
      affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints
        ((affineSpaceVariety K ι).openInclusion (coordinateOpen K S)) x)
          (e.symm (Sum.inr PUnit.unit)))) := by
  let C := (affineSpaceVariety K ι).openSubvariety (coordinateOpen K S)
  let Y := (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).openSubvariety
    (coordinateOpen K (coordinateStepInl T))
  let A := (affineSpaceVariety K κ).openSubvariety (coordinateOpen K T)
  let r : C.toOver ≅ Y.toOver := coordinateReindexIso K e S (coordinateStepInl T) h
  let c : Y.toOver ≅ A.toOver ⊗ (additiveVariety K).toOver := coordinateStepIso K T
  let iY := (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).openInclusion
    (coordinateOpen K (coordinateStepInl T))
  let y := Variety.mapPoints (X := C) (Y := Y) r.hom x
  have hs := coordinateStepIso_points K T y
  have hy := Variety.mapPoints_comp (X := C) (Y := Y)
    (Z := affineSpaceVariety K (κ ⊕ PUnit.{u+1})) r.hom iY x
  constructor
  · intro j
    let f : Y.toOver ⟶ (affineSpaceVariety K κ).toOver :=
      c.hom ≫ fst A.toOver (additiveVariety K).toOver ≫
        (affineSpaceVariety K κ).openInclusion (coordinateOpen K T)
    have hp := Variety.mapPoints_comp (X := C) (Y := Y) (Z := affineSpaceVariety K κ)
      r.hom f x
    have hr := coordinateReindexIso_points K e S (coordinateStepInl T) h x (Sum.inl j)
    exact (congrArg (fun z : (affineSpaceVariety K κ).points =>
        affineSpaceVarietyPointsEquiv K κ z j) hp).trans
      ((hs.1 j).symm.trans ((congrArg (fun z : (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).points =>
        affineSpaceVarietyPointsEquiv K (κ ⊕ PUnit.{u+1}) z (Sum.inl j)) hy).symm.trans hr))
  · let f : Y.toOver ⟶ (additiveVariety K).toOver :=
      c.hom ≫ snd A.toOver (additiveVariety K).toOver
    have hp := Variety.mapPoints_comp (X := C) (Y := Y) (Z := additiveVariety K) r.hom f x
    have hr := coordinateReindexIso_points K e S (coordinateStepInl T) h x
      (Sum.inr PUnit.unit)
    exact (congrArg (additivePointsEquiv K).symm hp).trans
      (hs.2.symm.trans ((congrArg (fun z : (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).points =>
        affineSpaceVarietyPointsEquiv K (κ ⊕ PUnit.{u+1}) z
          (Sum.inr PUnit.unit)) hy).symm.trans hr))

private theorem appendedUnitStep_points {K : Type u} [Field K] [IsAlgClosed K]
    {ι κ : Type u} [Finite ι] [Finite κ] (e : ι ≃ κ ⊕ PUnit.{u+1})
    (S : Finset ι) (T : Finset κ) (h : S.map e.toEmbedding = coordinateStepUnit T)
    (x : ((affineSpaceVariety K ι).openSubvariety (coordinateOpen K S)).points) :
    let A := (affineSpaceVariety K κ).openSubvariety (coordinateOpen K T)
    let r := coordinateReindexIso K e S (coordinateStepUnit T) h
    let c := coordinateUnitStepIso K T
    let B := (additiveVariety K).openSubvariety (additiveNonzero K)
    ((∀ j : κ, affineSpaceVarietyPointsEquiv K κ
      (Variety.mapPoints (r.hom ≫ c.hom ≫ fst A.toOver B.toOver ≫
        (affineSpaceVariety K κ).openInclusion (coordinateOpen K T)) x) j =
      affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints
        ((affineSpaceVariety K ι).openInclusion (coordinateOpen K S)) x) (e.symm (Sum.inl j))) ∧
    ((additivePointsEquiv K).symm (Variety.mapPoints
      (r.hom ≫ c.hom ≫ snd A.toOver B.toOver ≫
        (additiveVariety K).openInclusion (additiveNonzero K)) x) =
      affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints
        ((affineSpaceVariety K ι).openInclusion (coordinateOpen K S)) x)
          (e.symm (Sum.inr PUnit.unit)))) := by
  let C := (affineSpaceVariety K ι).openSubvariety (coordinateOpen K S)
  let Y := (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).openSubvariety
    (coordinateOpen K (coordinateStepUnit T))
  let A := (affineSpaceVariety K κ).openSubvariety (coordinateOpen K T)
  let r : C.toOver ≅ Y.toOver := coordinateReindexIso K e S (coordinateStepUnit T) h
  let B := (additiveVariety K).openSubvariety (additiveNonzero K)
  let c : Y.toOver ≅ A.toOver ⊗ B.toOver := coordinateUnitStepIso K T
  let iY := (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).openInclusion
    (coordinateOpen K (coordinateStepUnit T))
  let y := Variety.mapPoints (X := C) (Y := Y) r.hom x
  have hs := coordinateUnitStepIso_points K T y
  have hy := Variety.mapPoints_comp (X := C) (Y := Y)
    (Z := affineSpaceVariety K (κ ⊕ PUnit.{u+1})) r.hom iY x
  constructor
  · intro j
    let f : Y.toOver ⟶ (affineSpaceVariety K κ).toOver :=
      c.hom ≫ fst A.toOver B.toOver ≫
        (affineSpaceVariety K κ).openInclusion (coordinateOpen K T)
    have hp := Variety.mapPoints_comp (X := C) (Y := Y) (Z := affineSpaceVariety K κ)
      r.hom f x
    have hr := coordinateReindexIso_points K e S (coordinateStepUnit T) h x (Sum.inl j)
    exact (congrArg (fun z : (affineSpaceVariety K κ).points =>
        affineSpaceVarietyPointsEquiv K κ z j) hp).trans
      ((hs.1 j).symm.trans ((congrArg (fun z : (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).points =>
        affineSpaceVarietyPointsEquiv K (κ ⊕ PUnit.{u+1}) z (Sum.inl j)) hy).symm.trans hr))
  · let f : Y.toOver ⟶ (additiveVariety K).toOver :=
      c.hom ≫ snd A.toOver B.toOver ≫
        (additiveVariety K).openInclusion (additiveNonzero K)
    have hp := Variety.mapPoints_comp (X := C) (Y := Y) (Z := additiveVariety K) r.hom f x
    have hr := coordinateReindexIso_points K e S (coordinateStepUnit T) h x
      (Sum.inr PUnit.unit)
    exact (congrArg (additivePointsEquiv K).symm hp).trans
      (hs.2.symm.trans ((congrArg (fun z : (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).points =>
        affineSpaceVarietyPointsEquiv K (κ ⊕ PUnit.{u+1}) z
          (Sum.inr PUnit.unit)) hy).symm.trans hr))

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private theorem negativeStep_points (n : Fin word.length)
    (hn : n ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points) :
    let A := deodharParameters G (expression.take n.val)
    let e := deodharStepIndexSelected G expression n (Or.inr hn)
    ((∀ j : deodharIndex G (expression.take n.val),
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
        (Variety.mapPoints
          (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take n.val)))
          ((deodharNegativeStepIso G expression n hn).hom ≫
          fst A.toOver (additiveVariety K).toOver ≫
            deodharParameterInclusion G (expression.take n.val)) x) j =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (Variety.mapPoints
          (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take (n.val + 1))))
          (deodharParameterInclusion G (expression.take (n.val + 1))) x)
          (e.symm (Sum.inl j))) ∧
    ((additivePointsEquiv K).symm (Variety.mapPoints
      (X := deodharParameters G (expression.take (n.val + 1)))
      (Y := additiveVariety K)
      ((deodharNegativeStepIso G expression n hn).hom ≫
        snd A.toOver (additiveVariety K).toOver) x) =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (Variety.mapPoints
          (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take (n.val + 1))))
          (deodharParameterInclusion G (expression.take (n.val + 1))) x)
          (e.symm (Sum.inr PUnit.unit)))) := by
  classical
  let e := deodharStepIndexSelected G expression n (Or.inr hn)
  let S := deodharEqualPositions G (expression.take n.val)
  let C := deodharParameters G (expression.take (n.val + 1))
  let A := deodharParameters G (expression.take n.val)
  have hne : n ∉ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression :=
    fun he => hn.2 he.symm
  have h : (deodharEqualPositions G (expression.take (n.val + 1))).map e.toEmbedding =
      coordinateStepInl S :=
    (deodharEqualPositions_selected G expression n (Or.inr hn)).trans (by
      rw [ite_eq_right hne]
      rfl)
  let r := coordinateReindexIso K e
    (deodharEqualPositions G (expression.take (n.val + 1))) (coordinateStepInl S) h
  let c := coordinateStepIso K S
  have hf : (deodharNegativeStepIso G expression n hn).hom = r.hom ≫ c.hom := by
    unfold deodharNegativeStepIso
    rfl
  have hc := appendedStep_points (K := K) e
    (deodharEqualPositions G (expression.take (n.val + 1))) S h x
  constructor
  · intro j
    let p := fst A.toOver (additiveVariety K).toOver ≫
      deodharParameterInclusion G (expression.take n.val)
    have hp : (deodharNegativeStepIso G expression n hn).hom ≫ p =
        r.hom ≫ c.hom ≫ p :=
      (congrArg (fun f : C.toOver ⟶ A.toOver ⊗ (additiveVariety K).toOver => f ≫ p)
        hf).trans (Category.assoc r.hom c.hom p)
    exact (congrArg (fun f : C.toOver ⟶
        (affineSpaceVariety K (deodharIndex G (expression.take n.val))).toOver =>
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
        (Variety.mapPoints (X := C)
          (Y := affineSpaceVariety K (deodharIndex G (expression.take n.val))) f x) j)
      hp).trans (hc.1 j)
  · let p := snd A.toOver (additiveVariety K).toOver
    have hp : (deodharNegativeStepIso G expression n hn).hom ≫ p =
        r.hom ≫ c.hom ≫ p :=
      (congrArg (fun f : C.toOver ⟶ A.toOver ⊗ (additiveVariety K).toOver => f ≫ p)
        hf).trans (Category.assoc r.hom c.hom p)
    exact (congrArg (fun f : C.toOver ⟶ (additiveVariety K).toOver =>
      (additivePointsEquiv K).symm
        (Variety.mapPoints (X := C) (Y := additiveVariety K) f x)) hp).trans hc.2

private theorem equalStep_points (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points) :
    let A := deodharParameters G (expression.take n.val)
    let B := (additiveVariety K).openSubvariety (additiveNonzero K)
    let e := deodharStepIndexSelected G expression n (Or.inl hn)
    ((∀ j : deodharIndex G (expression.take n.val),
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
        (Variety.mapPoints
          (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take n.val)))
          ((deodharEqualStepIso G expression n hn).hom ≫
          fst A.toOver B.toOver ≫
            deodharParameterInclusion G (expression.take n.val)) x) j =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (Variety.mapPoints
          (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take (n.val + 1))))
          (deodharParameterInclusion G (expression.take (n.val + 1))) x)
          (e.symm (Sum.inl j))) ∧
    ((additivePointsEquiv K).symm (Variety.mapPoints
      (X := deodharParameters G (expression.take (n.val + 1)))
      (Y := additiveVariety K)
      ((deodharEqualStepIso G expression n hn).hom ≫
        snd A.toOver B.toOver ≫
        (additiveVariety K).openInclusion (additiveNonzero K)) x) =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (Variety.mapPoints
          (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take (n.val + 1))))
          (deodharParameterInclusion G (expression.take (n.val + 1))) x)
          (e.symm (Sum.inr PUnit.unit)))) := by
  classical
  let e := deodharStepIndexSelected G expression n (Or.inl hn)
  let S := deodharEqualPositions G (expression.take n.val)
  let C := deodharParameters G (expression.take (n.val + 1))
  let A := deodharParameters G (expression.take n.val)
  let B := (additiveVariety K).openSubvariety (additiveNonzero K)
  have h : (deodharEqualPositions G (expression.take (n.val + 1))).map e.toEmbedding =
      coordinateStepUnit S :=
    (deodharEqualPositions_selected G expression n (Or.inl hn)).trans (by
      rw [ite_eq_left hn]
      ext j
      simp only [coordinateStepUnit, coordinateStepInl, Finset.mem_insert, Finset.mem_map]
      rfl)
  let r := coordinateReindexIso K e
    (deodharEqualPositions G (expression.take (n.val + 1))) (coordinateStepUnit S) h
  let c := coordinateUnitStepIso K S
  have hf : (deodharEqualStepIso G expression n hn).hom = r.hom ≫ c.hom := by
    unfold deodharEqualStepIso
    rfl
  have hc := appendedUnitStep_points (K := K) e
    (deodharEqualPositions G (expression.take (n.val + 1))) S h x
  constructor
  · intro j
    let p := fst A.toOver B.toOver ≫
      deodharParameterInclusion G (expression.take n.val)
    have hp : (deodharEqualStepIso G expression n hn).hom ≫ p =
        r.hom ≫ c.hom ≫ p :=
      (congrArg (fun f : C.toOver ⟶ A.toOver ⊗ B.toOver => f ≫ p)
        hf).trans (Category.assoc r.hom c.hom p)
    exact (congrArg (fun f : C.toOver ⟶
        (affineSpaceVariety K (deodharIndex G (expression.take n.val))).toOver =>
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
        (Variety.mapPoints (X := C)
          (Y := affineSpaceVariety K (deodharIndex G (expression.take n.val))) f x) j)
      hp).trans (hc.1 j)
  · let p := snd A.toOver B.toOver ≫
      (additiveVariety K).openInclusion (additiveNonzero K)
    have hp : (deodharEqualStepIso G expression n hn).hom ≫ p =
        r.hom ≫ c.hom ≫ p :=
      (congrArg (fun f : C.toOver ⟶ A.toOver ⊗ B.toOver => f ≫ p)
        hf).trans (Category.assoc r.hom c.hom p)
    exact (congrArg (fun f : C.toOver ⟶ (additiveVariety K).toOver =>
      (additivePointsEquiv K).symm
        (Variety.mapPoints (X := C) (Y := additiveVariety K) f x)) hp).trans hc.2

/-- The decreasing-step identification retains every old selected coordinate. -/
theorem deodharNegativeStep_coord (n : Fin word.length)
    (hn : n ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points)
    (j : deodharIndex G (expression.take n.val)) :
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
        (Variety.mapPoints
          (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take n.val)))
          ((deodharNegativeStepIso G expression n hn).hom ≫
          fst (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver ≫
            deodharParameterInclusion G (expression.take n.val)) x) j =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (Variety.mapPoints
          (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take (n.val + 1))))
          (deodharParameterInclusion G (expression.take (n.val + 1))) x)
          ((deodharStepIndexSelected G expression n (Or.inr hn)).symm (Sum.inl j)) :=
  (negativeStep_points G expression n hn x).1 j

/-- The last decreasing-step coordinate is the parameter at the appended word position. -/
theorem deodharNegativeStep_last (n : Fin word.length)
    (hn : n ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points) :
    (additivePointsEquiv K).symm (Variety.mapPoints
      (X := deodharParameters G (expression.take (n.val + 1)))
      (Y := additiveVariety K)
      ((deodharNegativeStepIso G expression n hn).hom ≫
        snd (deodharParameters G (expression.take n.val)).toOver (additiveVariety K).toOver) x) =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (Variety.mapPoints
          (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take (n.val + 1))))
          (deodharParameterInclusion G (expression.take (n.val + 1))) x)
          ((deodharStepIndexSelected G expression n (Or.inr hn)).symm (Sum.inr PUnit.unit)) :=
  (negativeStep_points G expression n hn x).2

/-- The omitted-step identification retains every old selected coordinate. -/
theorem deodharEqualStep_coord (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points)
    (j : deodharIndex G (expression.take n.val)) :
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n.val))
        (Variety.mapPoints
          (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take n.val)))
          ((deodharEqualStepIso G expression n hn).hom ≫
          fst (deodharParameters G (expression.take n.val)).toOver
            ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver ≫
            deodharParameterInclusion G (expression.take n.val)) x) j =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (Variety.mapPoints
          (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take (n.val + 1))))
          (deodharParameterInclusion G (expression.take (n.val + 1))) x)
          ((deodharStepIndexSelected G expression n (Or.inl hn)).symm (Sum.inl j)) :=
  (equalStep_points G expression n hn x).1 j

/-- The last omitted-step coordinate is the parameter at the appended word position. -/
theorem deodharEqualStep_last (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G (expression.take (n.val + 1))).points) :
    (additivePointsEquiv K).symm (Variety.mapPoints
      (X := deodharParameters G (expression.take (n.val + 1)))
      (Y := additiveVariety K)
      ((deodharEqualStepIso G expression n hn).hom ≫
        snd (deodharParameters G (expression.take n.val)).toOver
          ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver ≫
        (additiveVariety K).openInclusion (additiveNonzero K)) x) =
      affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take (n.val + 1)))
        (Variety.mapPoints
          (X := deodharParameters G (expression.take (n.val + 1)))
          (Y := affineSpaceVariety K (deodharIndex G (expression.take (n.val + 1))))
          (deodharParameterInclusion G (expression.take (n.val + 1))) x)
          ((deodharStepIndexSelected G expression n (Or.inl hn)).symm (Sum.inr PUnit.unit)) :=
  (equalStep_points G expression n hn x).2

end SchubertGeometry
