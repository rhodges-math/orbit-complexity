import OrbitComplexity.GroupActions.Rosenlicht.RelationTranscendence
import OrbitComplexity.GroupActions.Rosenlicht.OrbitFibreDimension

/-!
# General orbit dimension and invariant rational functions

The dimension formula for the orbit relation and its general fibres identifies
orbit dimension on a nonempty open subset with relative transcendence degree.
Subtracting from the ambient dimension gives the transcendence degree of
invariant rational functions as the general orbit codimension.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- On a nonempty open subset, orbit dimension is the transcendence degree
of the function field over invariant rational functions. -/
theorem exists_open_orbit_trdeg :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    ∃ V : X.scheme.Opens, (V : Set X.scheme).Nonempty ∧
      ∀ x : X.points, X.pointMap x ∈ V → orbitNatDim H X x =
        (Algebra.trdeg (invariantField H X) X.scheme.functionField).toNat := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  obtain ⟨V, hV, hg⟩ := exists_open_orbit_fibre_dim H X
  refine ⟨V, hV, ?_⟩
  intro x hx
  have he := (hg x hx).2.symm.trans (orbitRelation_dim_add H X)
  rw [← X.natDim_cast] at he
  have hc := (ENat.WithBot.natCast_add_cancel).mp he
  have hn : (orbitNatDim H X x : WithBot ℕ∞) =
      ((Algebra.trdeg (invariantField H X) X.scheme.functionField).toNat : WithBot ℕ∞) := by
    rw [orbitNatDim_cast]
    exact hc
  exact ENat.natCast_inj.mp (WithBot.coe_inj.mp hn)

/-- On a nonempty open subset, orbit codimension is the transcendence degree
of invariant rational functions over the base field. -/
theorem exists_open_orbit_codim :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    ∃ V : X.scheme.Opens, (V : Set X.scheme).Nonempty ∧
      ∀ x : X.points, X.pointMap x ∈ V → orbitCodim H X x =
        ((Algebra.trdeg K (invariantField H X)).toNat : ℤ) := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : LocallyOfFiniteType (X.scheme ↘ Spec (.of K)) := X.locallyOfFiniteType
  have : Algebra.EssFiniteType K X.scheme.functionField := inferInstance
  have hs := invariantFunctionField_trdeg_sub K (X := X.scheme) (translationHom H X)
  change (Algebra.trdeg K (invariantField H X)).toNat =
    (Algebra.trdeg K X.scheme.functionField).toNat -
      (Algebra.trdeg (invariantField H X) X.scheme.functionField).toNat at hs
  rw [← X.natDim_functionField] at hs
  obtain ⟨V, hV, hg⟩ := exists_open_orbit_trdeg H X
  refine ⟨V, hV, ?_⟩
  intro x hx
  have hnle : (Algebra.trdeg (invariantField H X) X.scheme.functionField).toNat ≤ X.natDim := by
    rw [← hg x hx]
    exact orbitNatDim_le H X x
  change (X.natDim : ℤ) - (orbitNatDim H X x : ℤ) = _
  rw [hg x hx]
  exact (Int.ofNat_sub hnle).symm.trans (congrArg (fun n : ℕ ↦ (n : ℤ)) hs.symm)

end

end GroupActions.Variety
