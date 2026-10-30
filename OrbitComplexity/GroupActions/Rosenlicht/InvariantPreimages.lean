import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties
import OrbitComplexity.GroupActions.Varieties.RestrictedMorphisms
import OrbitComplexity.GroupActions.Varieties.OpenPoints

/-!
# Stable inverse images of open subsets

Inverse images of target opens under invariant morphisms inherit the group action.
Restriction preserves equality of images on the corresponding source open.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] {X Y : GroupActions.Variety K}

/-- Restricting a morphism over an open target commutes with the two open inclusions. -/
theorem restrictHom_comp_inclusion (f : X.toOver ⟶ Y.toOver) (V : Y.scheme.Opens) :
    restrictHom f V ≫ Y.openInclusion V = X.openInclusion (f.left ⁻¹ᵁ V) ≫ f := by
  apply Over.OverMorphism.ext
  exact morphismRestrict_ι f.left V

/-- Restricting a target open preserves equality of morphism images on the
corresponding open source. -/
theorem restrictHom_fibres (f : X.toOver ⟶ Y.toOver) (V : Y.scheme.Opens)
    (x y : (X.openSubvariety (f.left ⁻¹ᵁ V)).points) :
    mapPoints (restrictHom f V) x = mapPoints (restrictHom f V) y ↔
      mapPoints f (mapPoints (X.openInclusion (f.left ⁻¹ᵁ V)) x) =
        mapPoints f (mapPoints (X.openInclusion (f.left ⁻¹ᵁ V)) y) := by
  have hmap (z : (X.openSubvariety (f.left ⁻¹ᵁ V)).points) :
      mapPoints (Y.openInclusion V) (mapPoints (restrictHom f V) z) =
        mapPoints f (mapPoints (X.openInclusion (f.left ⁻¹ᵁ V)) z) := by
    rw [← mapPoints_comp, restrictHom_comp_inclusion, mapPoints_comp]
  constructor
  · intro h
    exact (hmap x).symm.trans ((congrArg (mapPoints (Y.openInclusion V)) h).trans (hmap y))
  · intro h
    apply mapPoints_injective_of_mono (Y.openInclusion V)
    exact (hmap x).trans (h.trans (hmap y).symm)

variable [IsAlgClosed K] (H : GroupActions.Variety K) [GrpObj H.toOver]
variable [ModObj H.toOver X.toOver]

private theorem preimageStable (f : X.toOver ⟶ Y.toOver)
    (hf : ∀ (h : H.points) (x : X.points), mapPoints f (h • x) = mapPoints f x)
    (V : Y.scheme.Opens) :
    ∀ (h : H.points) (z : (X.openSubvariety (f.left ⁻¹ᵁ V)).points),
      h • mapPoints (X.openInclusion (f.left ⁻¹ᵁ V)) z ∈
        Set.range (mapPoints (X.openInclusion (f.left ⁻¹ᵁ V))) := by
  intro h z
  rw [range_mapPoints, openInclusion_range]
  change f.left (X.pointMap (h • mapPoints (X.openInclusion (f.left ⁻¹ᵁ V)) z)) ∈ V
  rw [← pointMap_mapPoints, hf, pointMap_mapPoints]
  exact ((X.openSubvariety (f.left ⁻¹ᵁ V)).pointMap z).property

/-- The inverse image of an open subset under an invariant morphism inherits
the algebraic group action. -/
@[instance_reducible]
def invariantPreimageAction (f : X.toOver ⟶ Y.toOver)
    (hf : ∀ (h : H.points) (x : X.points), mapPoints f (h • x) = mapPoints f x)
    (V : Y.scheme.Opens) : ModObj H.toOver (X.openSubvariety (f.left ⁻¹ᵁ V)).toOver :=
  modObjOfInvariant H X _ (X.openInclusion (f.left ⁻¹ᵁ V)) (preimageStable H f hf V)

/-- The inclusion of an invariant inverse-image open is equivariant. -/
theorem invariantPreimage_isModHom (f : X.toOver ⟶ Y.toOver)
    (hf : ∀ (h : H.points) (x : X.points), mapPoints f (h • x) = mapPoints f x)
    (V : Y.scheme.Opens) :
    letI := invariantPreimageAction H f hf V
    IsModHom H.toOver (X.openInclusion (f.left ⁻¹ᵁ V)) :=
  modObjOfInvariant_isModHom H X _ (X.openInclusion (f.left ⁻¹ᵁ V))
    (preimageStable H f hf V)

/-- The inherited inverse-image action agrees with the ambient point action. -/
theorem invariantPreimage_smul (f : X.toOver ⟶ Y.toOver)
    (hf : ∀ (h : H.points) (x : X.points), mapPoints f (h • x) = mapPoints f x)
    (V : Y.scheme.Opens) (h : H.points)
    (z : (X.openSubvariety (f.left ⁻¹ᵁ V)).points) :
    letI := invariantPreimageAction H f hf V
    mapPoints (X.openInclusion (f.left ⁻¹ᵁ V)) (h • z) =
      h • mapPoints (X.openInclusion (f.left ⁻¹ᵁ V)) z :=
  modObjOfInvariant_smul H X _ (X.openInclusion (f.left ⁻¹ᵁ V))
    (preimageStable H f hf V) h z

end

end GroupActions.Variety
