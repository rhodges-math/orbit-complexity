import OrbitComplexity.GroupActions.Rosenlicht.FunctionFields
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Products of open charts

The product of two open immersions is an open immersion. Its image is the
intersection of the two inverse images of the chosen opens. A correspondence
with dominant projections therefore meets every pair of nonempty open charts.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens) (V : Y.Opens)

/-- The product of two open charts maps into the product of their ambient schemes. -/
def productOpenMap : pullback (U.ι ≫ f) (V.ι ≫ g) ⟶ pullback f g :=
  pullback.map _ _ _ _ U.ι V.ι (𝟙 S) (by simp) (by simp)

/-- A product of open chart inclusions is an open immersion. -/
instance productOpenMap_open : IsOpenImmersion (productOpenMap f g U V) := by
  dsimp only [productOpenMap]
  infer_instance

/-- The product-chart map preserves the first coordinate. -/
theorem productOpenMap_fst :
    productOpenMap f g U V ≫ pullback.fst f g =
      pullback.fst (U.ι ≫ f) (V.ι ≫ g) ≫ U.ι := by
  exact limit.lift_π _ _

/-- The product-chart map preserves the second coordinate. -/
theorem productOpenMap_snd :
    productOpenMap f g U V ≫ pullback.snd f g =
      pullback.snd (U.ι ≫ f) (V.ι ≫ g) ≫ V.ι := by
  exact limit.lift_π _ _

/-- A product chart consists of the points whose two coordinates lie in the chosen opens. -/
theorem productOpenMap_range :
    Set.range (productOpenMap f g U V) =
      pullback.fst f g ⁻¹' (U : Set X) ∩ pullback.snd f g ⁻¹' (V : Set Y) := by
  rw [productOpenMap, Scheme.Pullback.range_map, Scheme.Opens.range_ι, Scheme.Opens.range_ι]

/-- A correspondence with dominant projections meets the product of nonempty open charts. -/
theorem productChart_pullback_nonempty {Z : Scheme.{u}} [IrreducibleSpace Z]
    [IrreducibleSpace X] [IrreducibleSpace Y] (i : Z ⟶ pullback f g)
    [IsDominant (i ≫ pullback.fst f g)] [IsDominant (i ≫ pullback.snd f g)]
    (hU : (U : Set X).Nonempty) (hV : (V : Set Y).Nonempty) :
    Nonempty (pullback i (productOpenMap f g U V) : Scheme) := by
  have hu : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa only [Set.univ_inter] using hU)
  have hv : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr
      (by simpa only [Set.univ_inter] using hV)
  have hi : i (genericPoint Z) ∈ Set.range (productOpenMap f g U V) := by
    rw [productOpenMap_range]
    constructor
    · change (i ≫ pullback.fst f g) (genericPoint Z) ∈ U
      rw [map_genericPoint]
      exact hu
    · change (i ≫ pullback.snd f g) (genericPoint Z) ∈ V
      rw [map_genericPoint]
      exact hv
  have hz : genericPoint Z ∈ Set.range (pullback.fst i (productOpenMap f g U V)) := by
    rw [Scheme.Pullback.range_fst]
    exact hi
  obtain ⟨z, _⟩ := hz
  exact ⟨z⟩

end

end GroupActions
