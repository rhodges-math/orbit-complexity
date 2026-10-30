import OrbitComplexity.FrobeniusSplitting.Normality.Products.PointedFamilyOpaque
import OrbitComplexity.SchubertGeometry.Normality.Models.PairedFamilyData

/-! # A common pointed model for paired-source coordinates

The smooth auxiliary Borel product supplies the simultaneous affine
inputs. Its Hopf counit constructs one section over the common coefficient ring.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions FrobeniusSplitting
open scoped TensorProduct
namespace SchubertGeometry
noncomputable section

/-- A finite chosen coordinate diagram of the paired source has one
common pointed factor, preserving its nodes, arrows and all field fibres. -/
theorem pairedBSDH_family_model : SchubertGeometry.PointedFamilies.pairedFamily := by
  intro J _ _ K _ _ _ G a b S hS P F _ _ j _ e he
  let B := G.borelAlgebra ⊗[K] G.oppositeBorelAlgebra
  have : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  have : Algebra.Smooth K G.oppositeBorelAlgebra := G.oppositeBorel_smooth
  have : Algebra.Smooth K B := Algebra.Smooth.comp K G.borelAlgebra B
  have (i : J) : Algebra.Smooth K (F.obj i ⊗[K] B) :=
    pairedBSDH_tensor_smooth G a b (F.obj i) (j i)
  exact exists_pointed_family S hS P F e he (Bialgebra.counitAlgHom K B)

end
end SchubertGeometry
