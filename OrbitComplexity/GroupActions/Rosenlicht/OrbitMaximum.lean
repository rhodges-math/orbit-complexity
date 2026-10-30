import OrbitComplexity.GroupActions.Rosenlicht.GenericOrbitDimension
import OrbitComplexity.GroupActions.Rosenlicht.ProductDimension
import OrbitComplexity.GroupActions.Rosenlicht.RelationStabilizers
import OrbitComplexity.GroupActions.Varieties.ClosedFibres
import OrbitComplexity.GroupActions.Actions.OrbitDimension
import OrbitComplexity.GroupActions.Complexity.OrbitCodimension

/-!
# Maximum orbit dimension and invariant transcendence degree

The closed-point fibre bound for the orbit relation map bounds every orbit by
its general dimension. A general orbit therefore attains the maximum, and the
minimum orbit codimension equals the transcendence degree of invariant functions.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- Every orbit dimension is bounded by the relative transcendence degree over
invariant rational functions. -/
theorem orbitNatDim_le_relativeTrdeg (x : X.points) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    orbitNatDim H X x ≤
      (Algebra.trdeg (invariantField H X) X.scheme.functionField).toNat := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsIntegral (productVariety H X).scheme := product_integral H X
  have : IsIntegral (orbitRelationVariety H X).scheme :=
    isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
  obtain ⟨p, hp⟩ := relationDiagonalPoint_preimage H X x
  have hb := dim_le_add_fiber (productVariety H X) (orbitRelationVariety H X)
    (orbitRelationFactor H X) p
  rw [hp, relationStabilizer_dim H X x] at hb
  rw [← (productVariety H X).natDim_cast, ← (orbitRelationVariety H X).natDim_cast,
    ← (stabilizerVariety H X x).natDim_cast] at hb
  have hb' : ((productVariety H X).natDim : WithBot ℕ∞) ≤
      (((orbitRelationVariety H X).natDim + (stabilizerVariety H X x).natDim : ℕ) :
        WithBot ℕ∞) := by simpa only [Nat.cast_add] using hb
  have hn := ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp hb')
  rw [productVariety_natDim H X] at hn
  have hr := orbitRelation_dim_add H X
  rw [← (orbitRelationVariety H X).natDim_cast, ← X.natDim_cast] at hr
  have hr'' : ((orbitRelationVariety H X).natDim : WithBot ℕ∞) =
      ((X.natDim + (Algebra.trdeg (invariantField H X) X.scheme.functionField).toNat : ℕ) :
        WithBot ℕ∞) := by
    simpa only [Nat.cast_add] using hr
  have hr' : (orbitRelationVariety H X).natDim = X.natDim +
      (Algebra.trdeg (invariantField H X) X.scheme.functionField).toNat :=
    ENat.natCast_inj.mp (WithBot.coe_inj.mp hr'')
  rw [hr', orbitNatDim_add_stabilizer H X x] at hn
  omega

/-- On a nonempty open subset, every orbit has maximum dimension. -/
theorem exists_open_max_orbitDim :
    ∃ V : X.scheme.Opens, (V : Set X.scheme).Nonempty ∧
      ∀ x : X.points, X.pointMap x ∈ V →
        ∀ y : X.points, orbitNatDim H X y ≤ orbitNatDim H X x := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  obtain ⟨V, hV, hg⟩ := exists_open_orbit_trdeg H X
  refine ⟨V, hV, ?_⟩
  intro x hx y
  exact (orbitNatDim_le_relativeTrdeg H X y).trans_eq (hg x hx).symm

/-- Minimum orbit codimension is the transcendence degree of invariant rational
functions for an irreducible acting group. -/
theorem minOrbitCodim_eq_trdeg :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    minOrbitCodim H X = (Algebra.trdeg K (invariantField H X)).toNat := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  obtain ⟨V, hV, hc⟩ := exists_open_orbit_codim H X
  obtain ⟨W, hW, hm⟩ := exists_open_max_orbitDim H X
  have hgen (U : X.scheme.Opens) (hU : (U : Set X.scheme).Nonempty) :
      genericPoint X.scheme ∈ U :=
    ((genericPoint_spec X.scheme).mem_open_set_iff U.isOpen).mpr
      (by simpa only [Set.univ_inter] using hU)
  obtain ⟨x, hx⟩ := exists_point_mem_open X (V ⊓ W) ⟨genericPoint X.scheme,
    hgen V hV, hgen W hW⟩
  obtain ⟨y, hy⟩ := exists_orbitCodim_eq H X
  apply Int.ofNat_inj.mp
  apply le_antisymm
  · exact (minOrbitCodim_le H X x).trans_eq (hc x hx.1)
  · have ho := hm x hx.2 y
    have hcod : orbitCodim H X x ≤ orbitCodim H X y :=
      sub_le_sub_left (Int.ofNat_le.mpr ho) X.natDim
    exact (hc x hx.1).symm.le.trans (hcod.trans_eq hy)

end

end GroupActions.Variety
