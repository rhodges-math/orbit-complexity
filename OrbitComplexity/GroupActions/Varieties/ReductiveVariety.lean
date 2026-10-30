import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupPoints
import OrbitComplexity.ReductiveGroups.Groups.Cells.PointFlagSpace
import OrbitComplexity.GroupActions.Varieties.AffinePointTopology
import OrbitComplexity.GroupActions.Actions.Points
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Reductive groups as affine varieties

The spectrum of the coordinate Hopf algebra of a reductive group is a variety. Its rational
points identify with the convolution group of algebra homomorphisms into the base field.

## Main definitions

* `GroupActions.reductiveVariety`: the affine variety of a reductive group.
* `GroupActions.reductivePointsEquiv`: its rational points as coordinate algebra maps.
* `GroupActions.reductivePointsHomeomorph`: agreement of the rational-point topologies.
* `GroupActions.reductivePointsMulEquiv`: agreement with convolution multiplication.

## Main results

* `GroupActions.reductiveVarietyConnected`: the reductive variety is connected.
* `GroupActions.isClosed_borelPoints`: the Borel points form a closed subset.
* `GroupActions.isClosed_torusPoints`: the torus points form a closed subset.
-/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace GroupActions

noncomputable section

attribute [local instance] ReductiveGroups.pointZariskiTopology

universe u

variable {K : Type u} [Field K]

private def baseSpecIso : Over.mk (𝟙 (Spec (CommRingCat.of K))) ≅
    (Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of K)) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of K))) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
    simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp])

variable (G : ReductiveGroups.ReductiveGroupData K)

private theorem coordinateSmooth : Algebra.Smooth K G.coordinateAlgebra := G.reductive.smooth

attribute [local instance] coordinateSmooth

private theorem coordinateReduced : IsReduced G.coordinateAlgebra :=
  TauCeti.isReduced_of_smooth K G.coordinateAlgebra

attribute [instance] coordinateReduced

/-- The affine variety represented by the coordinate algebra of a reductive group. -/
def reductiveVariety : Variety K := affineVariety K G.coordinateAlgebra

/-- The variety of a reductive group is connected. -/
instance reductiveVarietyConnected : ConnectedSpace (reductiveVariety G).scheme :=
  TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace K
    (CommHopfAlgCat.of K G.coordinateAlgebra) G.reductive.geometricallyConnected

/-- The Hopf algebra structure makes the reductive variety a group object. -/
instance reductiveVarietyGroup : GrpObj (reductiveVariety G).toOver := by
  change GrpObj ((Spec (CommRingCat.of G.coordinateAlgebra)).asOver (Spec (CommRingCat.of K)))
  infer_instance

/-- Coordinate algebra maps identify the convolution points with the rational points. -/
def reductivePointsEquiv : G.points ≃ (reductiveVariety G).points :=
  (WithConv.equiv _).trans affinePointsEquiv

/-- The rational point associated to a convolution point is its spectrum map. -/
theorem reductivePointsEquiv_apply (g : G.points) :
    (reductivePointsEquiv G g).val = Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) := rfl

/-- The points of the chosen Borel subgroup form a closed subset of the group points. -/
theorem isClosed_borelPoints : IsClosed (G.borelPoints : Set G.points) := by
  have hclosed := ReductiveGroups.pointZariski_isClosed_zeroLocus
    (K := K) (G.borelIdeal.toIdeal : Set G.coordinateAlgebra)
  convert hclosed.preimage
    (continuous_induced_dom : Continuous (fun g : G.points => g.ofConv)) using 1
  ext g
  exact G.mem_borelPoints g

/-- The points of the chosen maximal torus form a closed subset of the group points. -/
theorem isClosed_torusPoints : IsClosed (G.torusPoints : Set G.points) := by
  have hclosed := ReductiveGroups.pointZariski_isClosed_zeroLocus
    (K := K) (G.torusIdeal.toIdeal : Set G.coordinateAlgebra)
  convert hclosed.preimage
    (continuous_induced_dom : Continuous (fun g : G.points => g.ofConv)) using 1
  ext g
  exact G.mem_torusPoints g

/-- The coordinate point identification is a homeomorphism for the Zariski topologies. -/
def reductivePointsHomeomorph : G.points ≃ₜ (reductiveVariety G).points where
  toEquiv := reductivePointsEquiv G
  continuous_toFun := (affineVarietyPointsHomeomorph K G.coordinateAlgebra).continuous.comp
    continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr
    (affineVarietyPointsHomeomorph K G.coordinateAlgebra).symm.continuous

private theorem pointsOverHom (g : G.points) :
    (reductiveVariety G).pointsEquivOverHom (reductivePointsEquiv G g) =
      (baseSpecIso (K := K)).hom ≫ Spec.mapMulEquiv g := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) =
    𝟙 _ ≫ Spec.map (CommRingCat.ofHom g.ofConv.toRingHom)
  exact (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Convolution multiplication agrees with the multiplication of scheme-valued points. -/
def reductivePointsMulEquiv : G.points ≃* (reductiveVariety G).points where
  toEquiv := reductivePointsEquiv G
  map_mul' g h := by
    apply (reductiveVariety G).pointsEquivOverHom.injective
    rw [Variety.pointsEquivOverHom_mul]
    calc
      _ = (baseSpecIso (K := K)).hom ≫ Spec.mapMulEquiv (g * h) := pointsOverHom G _
      _ = (baseSpecIso (K := K)).hom ≫ (Spec.mapMulEquiv g * Spec.mapMulEquiv h) :=
        congrArg (fun f => (baseSpecIso (K := K)).hom ≫ f) (map_mul Spec.mapMulEquiv g h)
      _ = ((baseSpecIso (K := K)).hom ≫ Spec.mapMulEquiv g) *
          ((baseSpecIso (K := K)).hom ≫ Spec.mapMulEquiv h) := MonObj.comp_mul _ _ _
      _ = _ := congrArg₂ (fun a b => a * b) (pointsOverHom G g).symm (pointsOverHom G h).symm

end

end GroupActions
