import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties
import OrbitComplexity.GroupActions.Actions.OrbitMap
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties
import OrbitComplexity.GroupActions.Varieties.OpenPoints

/-! # Saturation of open subvarieties

The union of the rational-point translates of an open set is an open subvariety.
It inherits the algebraic group action and is contained in every stable open
containing the initial open.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (H X : GroupActions.Variety K) [GrpObj H.toOver]
  [ModObj H.toOver X.toOver] (U : X.scheme.Opens)

/-- The saturation of an open set is the union of its rational-point translates. -/
def saturationOpen : X.scheme.Opens :=
  ⨆ h : H.points, (translateMorphism H X h⁻¹).left ⁻¹ᵁ U

/-- An open set is contained in its saturation. -/
theorem le_saturationOpen : U ≤ saturationOpen H X U := by
  intro x hx
  apply Opens.mem_iSup.mpr
  refine ⟨1, ?_⟩
  change (translateMorphism H X (1 : H.points)⁻¹).left x ∈ U
  rw [inv_one, translateMorphism_one]
  exact hx

/-- The saturation of a nonempty open set is nonempty. -/
theorem saturationOpen_nonempty (hU : (U : Set X.scheme).Nonempty) :
    (saturationOpen H X U : Set X.scheme).Nonempty :=
  hU.mono (le_saturationOpen H X U)

/-- Saturation lies in every translation-stable open set containing the original open. -/
theorem saturationOpen_le (V : X.scheme.Opens) (hUV : U ≤ V)
    (hV : ∀ h : H.points, (translateMorphism H X h).left ⁻¹ᵁ V = V) :
    saturationOpen H X U ≤ V := by
  apply iSup_le
  intro h
  calc
    (translateMorphism H X h⁻¹).left ⁻¹ᵁ U ≤
        (translateMorphism H X h⁻¹).left ⁻¹ᵁ V := fun _ hx ↦ hUV hx
    _ = V := hV _

/-- A rational point lies in the saturation exactly when one translate lies in the open. -/
theorem mem_saturationOpen (x : X.points) :
    X.pointMap x ∈ saturationOpen H X U ↔
      ∃ h : H.points, X.pointMap (h • x) ∈ U := by
  rw [saturationOpen, Opens.mem_iSup]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h⁻¹, ?_⟩
    change (translateMorphism H X h⁻¹).left (X.pointMap x) ∈ U at hh
    rw [← pointMap_mapPoints, mapPoints_translateMorphism] at hh
    exact hh
  · rintro ⟨h, hh⟩
    refine ⟨h⁻¹, ?_⟩
    change (translateMorphism H X (h⁻¹)⁻¹).left (X.pointMap x) ∈ U
    rw [inv_inv, ← pointMap_mapPoints, mapPoints_translateMorphism]
    exact hh

variable [IsAlgClosed K]

private theorem saturationStable :
    ∀ (h : H.points) (y : (X.openSubvariety (saturationOpen H X U)).points),
      h • mapPoints (X.openInclusion (saturationOpen H X U)) y ∈
        Set.range (mapPoints (X.openInclusion (saturationOpen H X U))) := by
  intro h y
  have hy : mapPoints (X.openInclusion (saturationOpen H X U)) y ∈
      Set.range (mapPoints (X.openInclusion (saturationOpen H X U))) := ⟨y, rfl⟩
  rw [range_mapPoints, openInclusion_range] at hy
  obtain ⟨g, hg⟩ := (mem_saturationOpen H X U _).mp hy
  rw [range_mapPoints, openInclusion_range]
  apply (mem_saturationOpen H X U _).mpr
  refine ⟨g * h⁻¹, ?_⟩
  simpa only [mul_smul, inv_smul_smul] using hg

/-- The saturation open subvariety inherits the ambient algebraic group action. -/
@[instance_reducible]
def saturationAction :
    ModObj H.toOver (X.openSubvariety (saturationOpen H X U)).toOver :=
  modObjOfInvariant H X _ (X.openInclusion (saturationOpen H X U))
    (saturationStable H X U)

/-- The inclusion of the saturation open subvariety is equivariant. -/
theorem saturationInclusion_isModHom :
    letI := saturationAction H X U
    IsModHom H.toOver (X.openInclusion (saturationOpen H X U)) :=
  modObjOfInvariant_isModHom H X _ (X.openInclusion (saturationOpen H X U))
    (saturationStable H X U)

/-- The inherited action on the saturation agrees with the ambient rational-point action. -/
theorem saturationAction_smul (h : H.points)
    (y : (X.openSubvariety (saturationOpen H X U)).points) :
    letI := saturationAction H X U
    mapPoints (X.openInclusion (saturationOpen H X U)) (h • y) =
      h • mapPoints (X.openInclusion (saturationOpen H X U)) y :=
  modObjOfInvariant_smul H X _ (X.openInclusion (saturationOpen H X U))
    (saturationStable H X U) h y

end

end GroupActions.Variety
