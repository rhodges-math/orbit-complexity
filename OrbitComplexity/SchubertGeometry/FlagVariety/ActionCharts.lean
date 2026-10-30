import OrbitComplexity.SchubertGeometry.FlagVariety.ChartMorphisms
import OrbitComplexity.GroupActions.Rosenlicht.ProductSections

/-! # Charts for the action on the flag variety

Pulling back the unipotent atlas gives local algebraic action morphisms on the product.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.MonObj

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The product of the reductive group and its flag variety. -/
abbrev flagActionProduct : GroupActions.Variety K :=
  GroupActions.Variety.productVariety (GroupActions.reductiveVariety G) (flagVariety G)

/-- The group projection from the action product. -/
def flagActionFst : (flagActionProduct G).toOver ⟶ (GroupActions.reductiveVariety G).toOver :=
  CartesianMonoidalCategory.fst _ _

/-- The flag projection from the action product. -/
def flagActionSnd : (flagActionProduct G).toOver ⟶ (flagVariety G).toOver :=
  CartesianMonoidalCategory.snd _ _

private theorem actionProductReduced : IsReduced (flagActionProduct G).toOver.left :=
  (flagActionProduct G).reduced

private theorem actionProductNoetherian : IsNoetherian (flagActionProduct G).toOver.left :=
  GroupActions.Variety.noetherian (flagActionProduct G)

private theorem actionProductSeparated : IsSeparated (flagActionProduct G).toSpec :=
  (flagActionProduct G).separated

private theorem actionProductFiniteType : LocallyOfFiniteType (flagActionProduct G).toSpec :=
  (flagActionProduct G).locallyOfFiniteType

private theorem actionProductQuasiCompact : QuasiCompact (flagActionProduct G).toSpec :=
  (flagActionProduct G).quasiCompact

attribute [local instance] actionProductReduced actionProductNoetherian actionProductSeparated
  actionProductFiniteType actionProductQuasiCompact

/-- A translated unipotent chart pulled back to the action product. -/
abbrev flagActionChartVariety (g : G.points) : GroupActions.Variety K where
  scheme := pullback (flagActionSnd G).left (flagChartMorphism G g).left
  toSpec := pullback.fst (flagActionSnd G).left (flagChartMorphism G g).left ≫
    (flagActionProduct G).toSpec
  reduced := isReduced_of_isOpenImmersion
    (pullback.fst (flagActionSnd G).left (flagChartMorphism G g).left)

/-- The open inclusion of an action chart into the action product. -/
def flagActionChartFst (g : G.points) :
    (flagActionChartVariety G g).toOver ⟶ (flagActionProduct G).toOver :=
  Over.homMk (pullback.fst (flagActionSnd G).left (flagChartMorphism G g).left) rfl

/-- An action chart is open in the group times flag variety. -/
instance flagActionChartFst_isOpen (g : G.points) :
    IsOpenImmersion (flagActionChartFst G g).left := by
  change IsOpenImmersion
    (pullback.fst (flagActionSnd G).left (flagChartMorphism G g).left)
  infer_instance
/-- The unipotent coordinate of an action chart. -/
def flagActionChartSnd (g : G.points) :
    (flagActionChartVariety G g).toOver ⟶ (GroupActions.oppositeUnipotentVariety G).toOver :=
  Over.homMk (pullback.snd (flagActionSnd G).left (flagChartMorphism G g).left) (by
    change pullback.snd (flagActionSnd G).left (flagChartMorphism G g).left ≫
        (GroupActions.oppositeUnipotentVariety G).toSpec =
      pullback.fst (flagActionSnd G).left (flagChartMorphism G g).left ≫
        (flagActionProduct G).toSpec
    have hc : (flagChartMorphism G g).left ≫ (flagVariety G).toSpec =
        (GroupActions.oppositeUnipotentVariety G).toSpec := (flagChartMorphism G g).w
    rw [← hc, ← Category.assoc, ← pullback.condition]
    rw [Category.assoc]
    exact congrArg (fun f => pullback.fst (flagActionSnd G).left (flagChartMorphism G g).left ≫ f)
      (flagActionSnd G).w)

/-- The two projections of an action chart commute with the flag-chart morphism. -/
theorem flagActionChart_condition (g : G.points) :
    flagActionChartSnd G g ≫ flagChartMorphism G g =
      flagActionChartFst G g ≫ flagActionSnd G := by
  apply Over.OverMorphism.ext
  exact pullback.condition.symm
/-- The local action multiplies the group coordinate by a unipotent representative. -/
def flagActionChartMorphism (g : G.points) :
    (flagActionChartVariety G g).toOver ⟶ (flagVariety G).toOver :=
  ((flagActionChartFst G g ≫ flagActionFst G) *
    (flagActionChartSnd G g ≫ flagChartMap G g)) ≫ flagQuotientMorphism G

/-- Pulling back the flag chart cover gives a cover of the action product. -/
def flagActionCover : Scheme.OpenCover.{u} (flagActionProduct G).scheme :=
  (flagSchemeCover G).pullback₁ (flagActionSnd G).left

end
end SchubertGeometry