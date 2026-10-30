import OrbitComplexity.SchubertGeometry.FlagVariety.Cocycle
import OrbitComplexity.GroupActions.Varieties.OpenCoverPoints

/-!
# Gluing the flag scheme

Translated opposite unipotent charts and their coordinate transitions give scheme gluing
data. The structure morphisms to the base field agree on overlaps, so they descend to the
glued scheme. The affine chart cover proves reducedness and local finite type.

## Main definitions

* `SchubertGeometry.flagGlueData`: the gluing data of the unipotent charts.
* `SchubertGeometry.flagScheme`: the glued scheme.
* `SchubertGeometry.flagSchemeToSpec`: its structure morphism over the base field.
* `SchubertGeometry.flagSchemeCover`: its open cover by unipotent charts.

## Main results

* `SchubertGeometry.flagScheme_reduced`: reducedness of the glued scheme.
* `SchubertGeometry.flagScheme_locallyOfFiniteType`: local finite type over the field.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private def transitionIso (g h : G.points) :
    (flagOverlapVariety G g h).toOver ≅ (flagOverlapVariety G h g).toOver where
  hom := flagTransition G g h
  inv := flagTransition G h g
  hom_inv_id := flagTransition_inv G g h
  inv_hom_id := flagTransition_inv G h g

set_option backward.isDefEq.respectTransparency.types false in
/-- The scheme gluing data from translated opposite unipotent charts. -/
def flagGlueData : Scheme.GlueData.{u} where
  J := G.points
  U _ := (GroupActions.oppositeUnipotentVariety G).scheme
  V ij := (flagOverlapVariety G ij.1 ij.2).scheme
  f g h := (flagOverlapInclusion G g h).left
  f_open g h := inferInstance
  f_id g := flagOverlapInclusion_self G g
  t g h := (transitionIso G g h).hom.left
  t_id g := by
    change (flagTransition G g g).left = Over.Hom.left (𝟙 (flagOverlapVariety G g g).toOver)
    exact congrArg Over.Hom.left (flagTransition_self G g)
  t' g h k := (flagTripleTransition G g h k).left
  t_fac g h k := by
    change (flagTripleTransition G g h k ≫ flagTripleSnd G h k g).left =
      (flagTripleFst G g h k ≫ flagTransition G g h).left
    exact congrArg Over.Hom.left (flagTripleTransition_snd G g h k)
  cocycle g h k := by
    change (flagTripleTransition G g h k ≫ flagTripleTransition G h k g ≫
      flagTripleTransition G k g h).left = Over.Hom.left (𝟙 (flagTripleVariety G g h k).toOver)
    exact congrArg Over.Hom.left (flagTripleTransition_cycle G g h k)

/-- The scheme obtained by gluing the translated opposite unipotent charts. -/
def flagScheme : Scheme.{u} := (flagGlueData G).glued

/-- The open immersion of a unipotent chart into the glued flag scheme. -/
def flagSchemeChart (g : G.points) :
    (GroupActions.oppositeUnipotentVariety G).scheme ⟶ flagScheme G :=
  (flagGlueData G).ι g

/-- The flag chart maps are open immersions. -/
instance flagSchemeChart_isOpen (g : G.points) : IsOpenImmersion (flagSchemeChart G g) :=
  (flagGlueData G).ι_isOpenImmersion g

private theorem chartBase_condition (ij : G.points × G.points) :
    (flagGlueData G).toGlueData.diagram.fst ij ≫
        (GroupActions.oppositeUnipotentVariety G).toSpec =
      (flagGlueData G).toGlueData.diagram.snd ij ≫
        (GroupActions.oppositeUnipotentVariety G).toSpec := by
  change (flagOverlapInclusion G ij.1 ij.2).left ≫
      (GroupActions.oppositeUnipotentVariety G).toSpec =
    ((flagTransition G ij.1 ij.2).left ≫ (flagOverlapInclusion G ij.2 ij.1).left) ≫
      (GroupActions.oppositeUnipotentVariety G).toSpec
  have hi : (flagOverlapInclusion G ij.1 ij.2).left ≫
      (GroupActions.oppositeUnipotentVariety G).toSpec =
        (flagOverlapVariety G ij.1 ij.2).toSpec := (flagOverlapInclusion G ij.1 ij.2).w
  have hj : (flagOverlapInclusion G ij.2 ij.1).left ≫
      (GroupActions.oppositeUnipotentVariety G).toSpec =
        (flagOverlapVariety G ij.2 ij.1).toSpec := (flagOverlapInclusion G ij.2 ij.1).w
  rw [hi, Category.assoc, hj]
  exact (flagTransition G ij.1 ij.2).w.symm

/-- The structure morphism of the glued flag scheme to its base field. -/
def flagSchemeToSpec : flagScheme G ⟶ Spec (CommRingCat.of K) :=
  Multicoequalizer.desc (flagGlueData G).toGlueData.diagram _
    (fun _ => (GroupActions.oppositeUnipotentVariety G).toSpec) (chartBase_condition G)

/-- Each glued chart is a morphism over the base field. -/
theorem flagSchemeChart_toSpec (g : G.points) :
    flagSchemeChart G g ≫ flagSchemeToSpec G =
      (GroupActions.oppositeUnipotentVariety G).toSpec := by
  unfold flagSchemeChart flagSchemeToSpec
  exact Multicoequalizer.π_desc (flagGlueData G).toGlueData.diagram _
    (fun _ => (GroupActions.oppositeUnipotentVariety G).toSpec) (chartBase_condition G) g

/-- The unipotent charts form an open cover of the flag scheme. -/
def flagSchemeCover : Scheme.OpenCover (flagScheme G) := (flagGlueData G).openCover

/-- The glued flag scheme is reduced because its unipotent charts are reduced. -/
instance flagScheme_reduced : IsReduced (flagScheme G) := by
  let : ∀ i : (flagGlueData G).openCover.I₀,
      IsReduced ((flagGlueData G).openCover.X i) := fun i =>
    inferInstanceAs (IsReduced (GroupActions.oppositeUnipotentVariety G).scheme)
  exact IsReduced.of_openCover (flagScheme G) (flagGlueData G).openCover

/-- The glued flag scheme is locally of finite type over its base field. -/
instance flagScheme_locallyOfFiniteType : LocallyOfFiniteType (flagSchemeToSpec G) := by
  let : ∀ i : (flagSchemeCover G).I₀, IsAffine ((flagSchemeCover G).X i) := fun i => by
    change IsAffine (Spec (CommRingCat.of G.oppositeUnipotentAlgebra))
    infer_instance
  apply HasRingHomProperty.of_source_openCover (P := @LocallyOfFiniteType.{u})
    (flagSchemeCover G)
  intro g
  change G.points at g
  have hfg : LocallyOfFiniteType ((flagSchemeCover G).f g ≫ flagSchemeToSpec G) := by
    change LocallyOfFiniteType (flagSchemeChart G g ≫ flagSchemeToSpec G)
    rw [flagSchemeChart_toSpec]
    infer_instance
  have : IsAffine ((flagSchemeCover G).X g) := by
    change IsAffine (Spec (CommRingCat.of G.oppositeUnipotentAlgebra))
    infer_instance
  exact HasRingHomProperty.appTop (@LocallyOfFiniteType.{u}) _ hfg

end
end SchubertGeometry
