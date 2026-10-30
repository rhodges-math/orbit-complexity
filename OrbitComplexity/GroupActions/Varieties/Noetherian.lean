import OrbitComplexity.GroupActions.Varieties.Morphisms
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Finiteness properties of varieties

Varieties over a field are Noetherian schemes. Every morphism between varieties over the
same field is of finite type and has constructible image.

## Main results

* `GroupActions.Variety.noetherian`: varieties are Noetherian schemes.
* `GroupActions.Variety.locallyOfFiniteType_hom`: variety morphisms are locally of finite type.
* `GroupActions.Variety.isConstructible_range`: images of variety morphisms are constructible.

## References

* Stacks Project, Tags 054J and 054K, Chevalley's theorem.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions.Variety

universe u

variable {K : Type u} [Field K]

/-- The underlying scheme of a variety over a field is Noetherian. -/
instance noetherian (X : GroupActions.Variety K) : IsNoetherian X.scheme where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.toSpec
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace X.toSpec

/-- A morphism between varieties over a field is locally of finite type. -/
theorem locallyOfFiniteType_hom {X Y : GroupActions.Variety K} (f : X.toOver ⟶ Y.toOver) :
    LocallyOfFiniteType f.left := by
  have hf : f.left ≫ Y.toSpec = X.toSpec := f.w
  have : LocallyOfFiniteType (f.left ≫ Y.toSpec) := hf.symm ▸ X.locallyOfFiniteType
  exact locallyOfFiniteType_of_comp (X := X.scheme) (Y := Y.scheme) f.left Y.toSpec

/-- The image in the underlying scheme of a variety morphism is constructible. -/
theorem isConstructible_range {X Y : GroupActions.Variety K} (f : X.toOver ⟶ Y.toOver) :
    IsConstructible (Set.range f.left) := by
  let g : X.scheme ⟶ Y.scheme := f.left
  have : LocallyOfFiniteType g := locallyOfFiniteType_hom f
  change IsConstructible (Set.range (g : X.scheme → Y.scheme))
  simpa only [Set.image_univ] using g.isConstructible_image IsConstructible.univ

end GroupActions.Variety
