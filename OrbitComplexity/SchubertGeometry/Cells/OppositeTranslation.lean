import OrbitComplexity.SchubertGeometry.Cells.OppositeDecomposition
import OrbitComplexity.GroupActions.Varieties.PointImageIso
import OrbitComplexity.GroupActions.Actions.OrbitMap

/-! # Longest translation of reduced Schubert varieties

The translated ordinary cell has the opposite-cell image. Its reduced closure
therefore identifies with the opposite Schubert variety over the base field.
-/

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups Topology
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Translation of the flag variety by the chosen longest representative. -/
def longestFlagIso : (flagVariety G).toOver ≅ (flagVariety G).toOver :=
  Variety.translationIso (reductiveVariety G) (flagVariety G)
    (reductivePointsMulEquiv G G.longestPoint)

private theorem flagTranslation_points (g h : G.points) :
    Variety.mapPoints (Variety.translationIso (reductiveVariety G) (flagVariety G)
      (reductivePointsMulEquiv G g)).hom
        (flagVarietyPointsEquiv G (flagProjection G h)) =
      flagVarietyPointsEquiv G (flagProjection G (g * h)) := by
  change Variety.mapPoints (Variety.translateMorphism (reductiveVariety G)
    (flagVariety G) (reductivePointsMulEquiv G g)) _ = _
  rw [Variety.mapPoints_translateMorphism, flagVarietyAction_points,
    ← flagProjection_smul]

private theorem longestFlag_inv_points (g : G.points) :
    Variety.mapPoints (longestFlagIso G).inv
        (flagVarietyPointsEquiv G (flagProjection G g)) =
      flagVarietyPointsEquiv G (flagProjection G (G.longestPoint⁻¹ * g)) := by
  change Variety.mapPoints (Variety.translateMorphism (reductiveVariety G)
    (flagVariety G) (reductivePointsMulEquiv G G.longestPoint)⁻¹) _ = _
  rw [← map_inv (reductivePointsMulEquiv G)]
  exact flagTranslation_points G G.longestPoint⁻¹ g

private def translatedCell (w : G.weylGroup) :
    (schubertCell G w).toOver ⟶ (flagVariety G).toOver :=
  schubertCellInclusion G w ≫ (longestFlagIso G).hom

private def translatedClosure (w : G.weylGroup) :
    (schubertVariety G w).toOver ⟶ (flagVariety G).toOver :=
  schubertInclusion G w ≫ (longestFlagIso G).hom

omit [IsAlgClosed K] [CharZero K] in
private theorem range_comp_iso {A B C : Variety K} (f : A.toOver ⟶ B.toOver)
    (e : B.toOver ≅ C.toOver) :
    Set.range (Variety.mapPoints (f ≫ e.hom)) =
      {z | Variety.mapPoints e.inv z ∈ Set.range (Variety.mapPoints f)} := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    rw [← Variety.mapPoints_comp, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [Variety.mapPoints_comp, ha, ← Variety.mapPoints_comp,
      Iso.inv_hom_id, Variety.mapPoints_id]

private theorem translated_orbit (w : G.weylGroup) (z : (flagVariety G).points) :
    z ∈ MulAction.orbit (oppositeBorelVariety G).points
        (weylFlagPoint G (G.longestElement * w)) ↔
      Variety.mapPoints (longestFlagIso G).inv z ∈
        MulAction.orbit (borelVariety G).points (weylFlagPoint G w) := by
  obtain ⟨q, rfl⟩ := (flagVarietyPointsEquiv G).surjective z
  obtain ⟨g, rfl⟩ := flagProjection_surjective G q
  rw [longestFlag_inv_points, mem_schubertOrbit_iff G w,
    mem_oppositeOrbit_iff G (G.longestElement * w)]
  simp only [inv_mul_cancel_left]

private theorem translated_cell_points (w : G.weylGroup) :
    Set.range (Variety.mapPoints (X := schubertCell G w) (Y := flagVariety G)
      (translatedCell G w)) =
      Set.range (Variety.mapPoints (X := oppositeSchubertCell G (G.longestElement * w))
        (Y := flagVariety G)
        (oppositeSchubertCellInclusion G (G.longestElement * w))) := by
  refine (range_comp_iso (A := schubertCell G w) (B := flagVariety G)
    (C := flagVariety G) (schubertCellInclusion G w) (longestFlagIso G)).trans ?_
  apply Set.ext
  intro z
  exact (Set.ext_iff.mp (schubertCell_points_range G w)
    (Variety.mapPoints (longestFlagIso G).inv z)).trans
      ((translated_orbit G w z).symm.trans
        (Set.ext_iff.mp (oppositeSchubertCell_points_range G (G.longestElement * w)) z).symm)

private theorem scheme_comp_range {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g) = g '' Set.range f := Set.range_comp g f

private theorem translated_schubert_range (w : G.weylGroup) :
    Set.range (translatedClosure G w).left =
      Set.range (oppositeSchubertInclusion G (G.longestElement * w)).left := by
  have hc := Variety.range_eq_of_mapPoints (X := schubertCell G w)
    (Y := oppositeSchubertCell G (G.longestElement * w)) (Z := flagVariety G)
    (translatedCell G w)
    (oppositeSchubertCellInclusion G (G.longestElement * w)) (translated_cell_points G w)
  calc
    _ = (longestFlagIso G).hom.left '' Set.range (schubertInclusion G w).left :=
      scheme_comp_range (schubertInclusion G w).left (longestFlagIso G).hom.left
    _ = (longestFlagIso G).hom.left '' closure (Set.range (schubertCellInclusion G w).left) :=
      congrArg (Set.image (longestFlagIso G).hom.left) (schubertInclusion_range G w)
    _ = closure ((longestFlagIso G).hom.left '' Set.range (schubertCellInclusion G w).left) :=
      (longestFlagIso G).hom.left.homeomorph.image_closure _
    _ = closure (Set.range (translatedCell G w).left) := congrArg closure
      (scheme_comp_range (schubertCellInclusion G w).left (longestFlagIso G).hom.left).symm
    _ = closure (Set.range
        (oppositeSchubertCellInclusion G (G.longestElement * w)).left) := congrArg closure hc
    _ = _ := (oppositeSchubertInclusion_range G (G.longestElement * w)).symm

private theorem translated_schubert_points (w : G.weylGroup) :
    Set.range (Variety.mapPoints (X := schubertVariety G w) (Y := flagVariety G)
      (translatedClosure G w)) =
      Set.range (Variety.mapPoints (X := oppositeSchubertVariety G (G.longestElement * w))
        (Y := flagVariety G)
        (oppositeSchubertInclusion G (G.longestElement * w))) := by
  exact (Variety.range_mapPoints (X := schubertVariety G w) (Y := flagVariety G)
      (translatedClosure G w)).trans
    ((congrArg (Set.preimage (flagVariety G).pointMap) (translated_schubert_range G w)).trans
      (Variety.range_mapPoints (X := oppositeSchubertVariety G (G.longestElement * w))
        (Y := flagVariety G) (oppositeSchubertInclusion G (G.longestElement * w))).symm)

private instance translatedSchubert_preimmersion (w : G.weylGroup) :
    IsPreimmersion (translatedClosure G w).left := by
  change IsPreimmersion ((schubertInclusion G w).left ≫ (longestFlagIso G).hom.left)
  infer_instance

/-- Longest translation identifies the reduced ordinary and opposite Schubert closures. -/
def oppositeSchubertIso (w : G.weylGroup) : (schubertVariety G w).toOver ≅
    (oppositeSchubertVariety G (G.longestElement * w)).toOver :=
  Variety.pointImageIso (X := schubertVariety G w)
    (Y := oppositeSchubertVariety G (G.longestElement * w)) (Z := flagVariety G)
    (translatedClosure G w)
    (oppositeSchubertInclusion G (G.longestElement * w)) (translated_schubert_points G w)

/-- The opposite Schubert isomorphism retains the translated flag inclusion. -/
theorem oppositeSchubertIso_comp (w : G.weylGroup) :
    (oppositeSchubertIso G w).hom ≫ oppositeSchubertInclusion G (G.longestElement * w) =
      schubertInclusion G w ≫ (longestFlagIso G).hom :=
  Variety.pointImageIso_hom_comp _ _ (translated_schubert_points G w)

end
end SchubertGeometry
