import OrbitComplexity.GroupActions.Varieties.RestrictedFibres

/-! # Dimensions of restricted fibres

Restricting a scheme morphism to open subsets embeds each restricted fibre in the
corresponding fibre of the original morphism, so its Krull dimension cannot increase.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

/-- A restriction to open source and target subsets cannot increase fibre dimension. -/
theorem fibre_dim_resLE_le {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (y : U) :
    topologicalKrullDim ((f.resLE U V h).fiber y) ≤
      topologicalKrullDim (f.fiber (y : Y)) := by
  let g : ((f.resLE U V h) ⁻¹' {y}) → (f ⁻¹' {(y : Y)}) := fun z ↦
    ⟨z.1.1, by
      change f z.1.1 = (y : Y)
      have hz : f.resLE U V h z.1 = y := z.2
      exact (Scheme.Hom.coe_resLE_apply f h z.1).symm.trans (congrArg Subtype.val hz)⟩
  have hg : IsEmbedding g := by
    apply IsEmbedding.subtypeVal.of_comp_iff.mp
    change IsEmbedding (fun z : ((f.resLE U V h) ⁻¹' {y}) ↦ z.1.1)
    exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  calc
    _ = topologicalKrullDim ((f.resLE U V h) ⁻¹' {y}) :=
      ((f.resLE U V h).fiberHomeo y).isHomeomorph.topologicalKrullDim_eq
    _ ≤ topologicalKrullDim (f ⁻¹' {(y : Y)}) := hg.isInducing.topologicalKrullDim_le
    _ = _ := (f.fiberHomeo (y : Y)).isHomeomorph.topologicalKrullDim_eq.symm

end

end GroupActions
