import OrbitComplexity.GroupActions.Rosenlicht.ProductFibres
import OrbitComplexity.GroupActions.Varieties.GenericBaseFibres
import OrbitComplexity.GroupActions.Varieties.FiniteDimension

/-!
# Dimension of products of irreducible varieties

A nonempty open subset over an algebraically closed field contains a rational
point. Evaluating the generic fibre dimension formula for the product projection
at such a point gives the sum of the dimensions of its factors.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory Topology

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A nonempty open subset of a variety contains a rational point. -/
theorem exists_point_mem_open (X : GroupActions.Variety K) (U : X.scheme.Opens)
    (hU : (U : Set X.scheme).Nonempty) : ∃ x : X.points, X.pointMap x ∈ U := by
  have : JacobsonSpace X.scheme := LocallyOfFiniteType.jacobsonSpace X.toSpec
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hU U.isOpen.isLocallyClosed
  obtain ⟨x, hx⟩ := X.pointsEquivClosedPoints.surjective ⟨z, hzc⟩
  refine ⟨x, ?_⟩
  have hval : X.pointMap x = z := congrArg Subtype.val hx
  rw [hval]
  exact hz

variable (H X : GroupActions.Variety K)
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- The dimension of a product of irreducible varieties is the sum of their dimensions. -/
theorem productVariety_dim : (productVariety H X).dim = H.dim + X.dim := by
  have : IsIntegral (productVariety H X).scheme := product_integral H X
  obtain ⟨h, _⟩ := exists_point_mem_open H ⊤ Set.univ_nonempty
  let p : (productVariety H X).toOver ⟶ X.toOver := snd H.toOver X.toOver
  have : Surjective p.left := by
    constructor
    intro y
    refine ⟨(pointSection H X h).left y, ?_⟩
    exact congrArg (fun f : X.toOver ⟶ X.toOver ↦ f.left y) (pointSection_snd H X h)
  obtain ⟨V, hV, hd⟩ := exists_open_dim_add (productVariety H X) X p
  obtain ⟨x, hx⟩ := exists_point_mem_open X V hV
  have he := (productSecondFibreHomeomorph H X x).isHomeomorph.topologicalKrullDim_eq
  calc
    (productVariety H X).dim = X.dim +
        topologicalKrullDim ((snd H.toOver X.toOver).left.fiber (X.pointMap x)) := hd _ hx
    _ = X.dim + H.dim := congrArg (fun d ↦ X.dim + d) he
    _ = H.dim + X.dim := add_comm _ _

/-- Natural dimensions add in a product of irreducible varieties. -/
theorem productVariety_natDim : (productVariety H X).natDim = H.natDim + X.natDim := by
  have : IsIntegral (productVariety H X).scheme := product_integral H X
  have hn : ((productVariety H X).natDim : WithBot ℕ∞) =
      ((H.natDim + X.natDim : ℕ) : WithBot ℕ∞) := by
    rw [(productVariety H X).natDim_cast, Nat.cast_add, H.natDim_cast, X.natDim_cast]
    exact productVariety_dim H X
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp hn)

end

end GroupActions.Variety
