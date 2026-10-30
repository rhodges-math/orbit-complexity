import OrbitComplexity.SchubertGeometry.Deodhar.PrefixCharts
import OrbitComplexity.SchubertGeometry.Deodhar.ProjectionActions

/-! # Torus-equivariant prefix projections

The increasing-cell projections respect the Borel actions. The ordinary torus actions agree
with their restrictions, so every reduced-word prefix projection is torus equivariant.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def torusBorelPoint (t : (torusVariety G).points) : (borelVariety G).points :=
  (borelPointsMulEquiv G).symm
    ⟨torusPointsMulEquiv G t, G.torus_le_borel (torusPointsMulEquiv G t).property⟩

omit [CharZero K] in
private theorem torusBorelPoint_val (t : (torusVariety G).points) :
    (borelPointsMulEquiv G (torusBorelPoint G t) : G.points) =
      (torusPointsMulEquiv G t : G.points) :=
  congrArg Subtype.val ((borelPointsMulEquiv G).apply_symm_apply _)

private theorem torus_cell_smul (w : G.weylGroup) (t : (torusVariety G).points)
    (x : (schubertCell G w).points) : t • x = torusBorelPoint G t • x := by
  apply Variety.mapPoints_injective_of_mono (schubertCellInclusion G w)
  rw [schubertCell_torus_smul, schubertCell_smul]
  let q := (flagVarietyPointsEquiv G).symm
    (Variety.mapPoints (schubertCellInclusion G w) x)
  have hq : flagVarietyPointsEquiv G q =
      Variety.mapPoints (schubertCellInclusion G w) x := Equiv.apply_symm_apply _ _
  rw [← hq, torusFlag_smul, borelFlag_smul, torusBorelPoint_val]

private theorem rankOneProjection_torus (w : G.weylGroup) (i : G.rootBase.support)
    (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i)) :
    IsModHom (torusVariety G).toOver (rankOneCellProjection G w i hw) := by
  apply Variety.isModHom_of_points (torusVariety G) _ _ _
  intro t x
  calc
    _ = Variety.mapPoints (rankOneCellProjection G w i hw) (torusBorelPoint G t • x) :=
      congrArg (Variety.mapPoints (rankOneCellProjection G w i hw))
        (torus_cell_smul G _ t x)
    _ = torusBorelPoint G t • Variety.mapPoints (rankOneCellProjection G w i hw) x :=
      rankOneProjection_smul G w i hw (torusBorelPoint G t) x
    _ = _ := (torus_cell_smul G w t _).symm

private theorem equivariant_of_comp {C : Type*} [Category C]
    [CartesianMonoidalCategory C] (H X Y Z : C) [MonObj H]
    [ModObj H X] [ModObj H Y] [ModObj H Z]
    (f : X ⟶ Y) (i : Y ⟶ Z) (j : X ⟶ Z) [Mono i]
    [IsModHom H i] [IsModHom H j] (h : f ≫ i = j) : IsModHom H f := by
  constructor
  apply (cancel_mono i).mp
  rw [Category.assoc, h, IsModHom.smul_hom]
  rw [Category.assoc, IsModHom.smul_hom, ← Category.assoc,
    ← MonoidalCategory.MonoidalLeftAction.actionHomRight_comp, h]

private theorem cell_cast_torus {a b : G.weylGroup} (h : a = b) :
    IsModHom (torusVariety G).toOver
      (eqToHom (congrArg (fun w : G.weylGroup => (schubertCell G w).toOver) h)) := by
  subst b
  exact inferInstanceAs (IsModHom (torusVariety G).toOver (𝟙 (schubertCell G a).toOver))

variable (word : List G.rootBase.support)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)

private theorem wordCellStep_torus (n : ℕ) :
    IsModHom (torusVariety G).toOver (wordCellStep G word hred n) := by
  by_cases hn : n < word.length
  · let hi := wordCell_ascent G word hred n hn
    rw [wordCellStep_eq G word hred n hn hi]
    have : Mono (schubertCellInclusion G
        (simpleWeylWord G.rootBase (word.take (n + 1)))) := Over.mono_of_mono_left _
    have : IsModHom (torusVariety G).toOver (wordCellExtensionIso G word n hn).hom :=
      equivariant_of_comp (torusVariety G).toOver _ _ _
        (wordCellExtensionIso G word n hn).hom
        (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take (n + 1))))
        (schubertCellInclusion G (simpleWeylWord G.rootBase (word.take n) *
          RootPairing.weylGroup.ofIdx G.rootSystem word[n]))
        (wordCellExtensionIso_flag G word n hn)
    have := rankOneProjection_torus G (simpleWeylWord G.rootBase (word.take n)) word[n] hi
    infer_instance
  · unfold wordCellStep
    rw [dite_eq_right hn]
    exact cell_cast_torus G (by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)])

/-- Projection between reduced-word prefix cells respects the ordinary torus actions. -/
instance wordCellProjection_torus {i j : ℕ} (h : i ≤ j) :
    IsModHom (torusVariety G).toOver (wordCellProjection G word hred h) := by
  induction j, h using Nat.le_induction with
  | base =>
    rw [wordCellProjection_self]
    infer_instance
  | succ j hj ih =>
    rw [wordCellProjection_succ G word hred hj]
    have := wordCellStep_torus G word hred j
    have := ih
    infer_instance

end
end SchubertGeometry
