import OrbitComplexity.GroupActions.Rosenlicht.PointFibres

/-!
# Fibres of an open restriction

The fibre of a morphism restricted to an open subset embeds into the original
fibre. Its inclusion agrees with the open immersion on underlying scheme points.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

variable {R X : Scheme.{u}} (f : R ⟶ X) (U : R.Opens) (x : X)

private def openFibreLift : ((U.ι ≫ f) ⁻¹' {x}) → (f ⁻¹' {x}) :=
  fun z ↦ ⟨U.ι z.val, z.property⟩

private lemma openFibreLift_isEmbedding : IsEmbedding (openFibreLift f U x) := by
  have hi := U.ι.isOpenEmbedding.isEmbedding.comp
    (IsEmbedding.subtypeVal : IsEmbedding
      (Subtype.val : ((U.ι ≫ f) ⁻¹' {x}) → (U : Scheme)))
  let T := f ⁻¹' {x}
  have hm : ∀ z : ((U.ι ≫ f) ⁻¹' {x}), U.ι z.val ∈ T := fun z ↦ z.property
  exact hi.codRestrict T hm

/-- The fibre of an open restriction maps into the original fibre. -/
def openFibreMap : (U.ι ≫ f).fiber x → f.fiber x :=
  fun z ↦ (f.fiberHomeo x).symm (openFibreLift f U x ((U.ι ≫ f).fiberHomeo x z))

/-- The fibre inclusion commutes with the open immersion. -/
theorem openFibreMap_apply (z : (U.ι ≫ f).fiber x) :
    f.fiberι x (openFibreMap f U x z) = U.ι ((U.ι ≫ f).fiberι x z) := by
  simp only [openFibreMap, Scheme.Hom.fiberι_fiberHomeo_symm, openFibreLift,
    Scheme.Hom.fiberHomeo_apply]

/-- Restricting the source to an open subset embeds every fibre. -/
theorem openFibreMap_isEmbedding : IsEmbedding (openFibreMap f U x) :=
  (f.fiberHomeo x).symm.isEmbedding.comp
    ((openFibreLift_isEmbedding f U x).comp ((U.ι ≫ f).fiberHomeo x).isEmbedding)

end

end GroupActions
