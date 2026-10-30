import OrbitComplexity.GroupActions.Actions.Translations
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties
import TauCeti.AlgebraicGeometry.Group.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import TauCeti.Topology.NoetherianSpace.ConnectedComponents

/-! # Connected components of group varieties

A reduced group variety over an algebraically closed field is smooth. Its connected
components are open integral subvarieties.

## Main definitions

* `GroupActions.groupComponent`: the open subvariety on a connected component.
* `GroupActions.identityComponent`: the component containing the unit point.

## Main results

* `GroupActions.groupComponent_integral`: every connected component is integral.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open scoped CategoryTheory.MonObj

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H : Variety K) [GrpObj H.toOver]

/-- A reduced group variety over an algebraically closed field is smooth. -/
instance groupVariety_smooth : Smooth H.toSpec :=
  TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced H.toSpec

/-- The open subvariety on the connected component of a scheme point. -/
def groupComponent (x : H.scheme) : Variety K :=
  H.openSubvariety ⟨connectedComponent x, isOpen_connectedComponent⟩

/-- A group component is connected. -/
instance groupComponent_connected (x : H.scheme) : ConnectedSpace (groupComponent H x).scheme :=
  Subtype.connectedSpace isConnected_connectedComponent

/-- Every connected component of a group variety is integral. -/
instance groupComponent_integral (x : H.scheme) : IsIntegral (groupComponent H x).scheme := by
  have : Smooth (groupComponent H x).toSpec := by
    let U : H.scheme.Opens := ⟨connectedComponent x, isOpen_connectedComponent⟩
    change Smooth (U.ι ≫ H.toSpec)
    infer_instance
  have : ∀ z : (groupComponent H x).scheme,
      IsRegularLocalRing ((groupComponent H x).scheme.presheaf.stalk z) :=
    TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth (groupComponent H x).toSpec
  exact TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk _

/-- The identity component is the component containing the unit rational point. -/
def identityComponent : Variety K := groupComponent H (H.pointMap 1)

/-- The identity component is integral. -/
instance identityComponent_integral : IsIntegral (identityComponent H).scheme :=
  inferInstanceAs (IsIntegral (groupComponent H (H.pointMap 1)).scheme)

/-- The identity component is connected. -/
instance identityComponent_connected : ConnectedSpace (identityComponent H).scheme :=
  inferInstanceAs (ConnectedSpace (groupComponent H (H.pointMap 1)).scheme)

/-- The identity component is included as an open subvariety. -/
def identityInclusion : (identityComponent H).toOver ⟶ H.toOver :=
  H.openInclusion ⟨connectedComponent (H.pointMap 1), isOpen_connectedComponent⟩

/-- The inclusion of the identity component is an open immersion. -/
instance identityInclusion_isOpen : IsOpenImmersion (identityInclusion H).left :=
  inferInstanceAs (IsOpenImmersion
    (H.openInclusion ⟨connectedComponent (H.pointMap 1), isOpen_connectedComponent⟩).left)

/-- The identity-component inclusion is a monomorphism over the base field. -/
instance identityInclusion_mono : Mono (identityInclusion H) := Over.mono_of_mono_left _

omit [IsAlgClosed K] in
/-- The identity-component inclusion has precisely the component of the unit as image. -/
theorem identityInclusion_range :
    Set.range ((identityInclusion H).left : (identityComponent H).scheme → H.scheme) =
      connectedComponent (H.pointMap 1) :=
  H.openInclusion_range _

omit [IsAlgClosed K] in
/-- The unit morphism is the morphism underlying the unit rational point. -/
theorem unitPoint_left : η[H.toOver].left = (1 : H.points).val := by
  have he := Variety.pointsEquivOverHom_one H
  change H.pointsEquivOverHom 1 =
    CartesianMonoidalCategory.toUnit _ ≫ η[H.toOver] at he
  have ht : CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (.of K)))) = 𝟙 _ :=
    CartesianMonoidalCategory.toUnit_unique _ _
  rw [ht, Category.id_comp] at he
  exact congrArg Over.Hom.left he.symm

end

end GroupActions
