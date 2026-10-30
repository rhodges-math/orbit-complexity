import OrbitComplexity.GroupActions.Rosenlicht.ActionFields
import OrbitComplexity.GroupActions.Varieties.Dimension

/-!
# Generic points of product sections

Products of irreducible varieties over an algebraically closed field are
varieties. Sections of the second projection attached to rational points of the
first factor send the generic point of the second factor to a dense set.

## Main definitions

* `Variety.productVariety`: the integral product as a variety.
* `Variety.pointSection`: the section attached to a rational point of the first factor.

## Main results

* `Variety.pointSection_generic_dense`: generic points of point sections are dense.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The product of two irreducible varieties, with its reduced finite-type structure. -/
abbrev productVariety : GroupActions.Variety K where
  scheme := (H.toOver ⊗ X.toOver).left
  toSpec := (H.toOver ⊗ X.toOver).hom
  reduced := by
    have := product_integral H X
    infer_instance
  separated := by
    change IsSeparated (Limits.pullback.fst H.toSpec X.toSpec ≫ H.toSpec)
    infer_instance
  locallyOfFiniteType := by
    change LocallyOfFiniteType (Limits.pullback.fst H.toSpec X.toSpec ≫ H.toSpec)
    infer_instance
  quasiCompact := by
    change QuasiCompact (Limits.pullback.fst H.toSpec X.toSpec ≫ H.toSpec)
    infer_instance

/-- A rational point of the first factor gives a section of the second projection. -/
def pointSection (h : H.points) : X.toOver ⟶ (productVariety H X).toOver :=
  lift (toUnit X.toOver ≫ H.pointsEquivOverHom h) (𝟙 X.toOver)

/-- A point section is a right inverse of the second projection. -/
@[simp]
theorem pointSection_snd (h : H.points) :
    pointSection H X h ≫ snd H.toOver X.toOver = 𝟙 X.toOver :=
  lift_snd _ _

private lemma toUnit_base (S : Scheme.{u}) :
    toUnit (Over.mk (𝟙 S)) = 𝟙 (Over.mk (𝟙 S)) := toUnit_unique _ _

private lemma point_in_section (z : (productVariety H X).points) :
    ∃ (h : H.points) (x : X.points), mapPoints (pointSection H X h) x = z := by
  let zOver := (productVariety H X).pointsEquivOverHom z
  let h := H.pointsEquivOverHom.symm (zOver ≫ fst H.toOver X.toOver)
  let x := X.pointsEquivOverHom.symm (zOver ≫ snd H.toOver X.toOver)
  refine ⟨h, x, ?_⟩
  apply (productVariety H X).pointsEquivOverHom.injective
  change X.pointsEquivOverHom x ≫ pointSection H X h = zOver
  apply CartesianMonoidalCategory.hom_ext
  · dsimp only [pointSection]
    rw [Category.assoc, lift_fst, ← Category.assoc, comp_toUnit,
      toUnit_base, Category.id_comp]
    exact H.pointsEquivOverHom.apply_symm_apply _
  · dsimp only [pointSection]
    rw [Category.assoc, lift_snd, Category.comp_id]
    exact X.pointsEquivOverHom.apply_symm_apply _

/-- The images of the generic point under all rational point sections are dense
in the product of irreducible varieties. -/
theorem pointSection_generic_dense :
    Dense (Set.range (fun h : H.points ↦
      (pointSection H X h).left (genericPoint X.scheme))) := by
  let P := productVariety H X
  have hd : Dense (Set.range P.pointMap) := by
    rw [dense_iff_closure_eq]
    simpa only [pointClosure, Set.image_univ] using P.pointClosure_univ
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨_, ⟨z, rfl⟩, hzU⟩ := hd.exists_mem_open hU hUne
  obtain ⟨h, x, hxz⟩ := point_in_section H X z
  have hpre : ((pointSection H X h).left ⁻¹' U).Nonempty := by
    refine ⟨X.pointMap x, ?_⟩
    change (pointSection H X h).left (X.pointMap x) ∈ U
    rw [← pointMap_mapPoints, hxz]
    exact hzU
  have hgen : (pointSection H X h).left (genericPoint X.scheme) ∈ U :=
    ((genericPoint_spec X.scheme).mem_open_set_iff
      (hU.preimage (pointSection H X h).left.continuous)).mpr (by simpa using hpre)
  exact ⟨_, hgen, ⟨h, rfl⟩⟩

end

end GroupActions.Variety
