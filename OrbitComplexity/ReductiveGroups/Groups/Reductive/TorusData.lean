import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupSubgroups
import TauCeti.Algebra.AlgebraicGroup.Torus.Reductive
import TauCeti.Algebra.AlgebraicGroup.Borel.Existence

/-!
# Split tori as reductive group data

A torus is its own maximal torus and its own Borel subgroup. The coordinate
Hopf algebra of a finite-rank split torus therefore forms reductive group data
with both defining ideals zero and with the identity splitting map.

## Main definitions

* `ReductiveGroups.SplitTorus.groupData`: the split torus on a finite index type.
* `ReductiveGroups.ReductiveGroupData.torusData`: the chosen maximal torus.

## Main results

* `ReductiveGroups.torus_isMaximalTorus_bot`: a torus is its own maximal torus.
* `ReductiveGroups.torus_isBorel_bot`: a torus is its own Borel subgroup.
-/

noncomputable section

namespace ReductiveGroups

open TauCeti CategoryTheory

universe u

variable {K : Type u} [Field K]

/-- A torus is its own maximal torus. -/
theorem torus_isMaximalTorus_bot (H : FiniteTypeCommHopfAlgCat.{u, u} K)
    (hH : torusCommHopfAlgProperty K H) : HopfIdeal.IsMaximalTorus K H.obj ⊥ := by
  refine ⟨?_, fun _ _ _ => bot_le⟩
  exact (torusCommHopfAlgProperty K).prop_of_iso
    (FiniteTypeCommHopfAlgCat.quotientBotIso H).symm hH

private theorem torus_isBorelOverAlgClosed_bot [IsAlgClosed K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} K) (hH : torusCommHopfAlgProperty K H) :
    HopfIdeal.IsBorelOverAlgClosed K H ⊥ := by
  refine ⟨inferInstance, ?_, fun _ _ _ => bot_le⟩
  apply HopfIdeal.torusCommHopfAlgProperty.isBorelCandidate
  exact (torusCommHopfAlgProperty K).prop_of_iso
    (FiniteTypeCommHopfAlgCat.quotientBotIso H).symm hH

/-- A torus is its own Borel subgroup over every field. -/
theorem torus_isBorel_bot (H : FiniteTypeCommHopfAlgCat.{u, u} K)
    (hH : torusCommHopfAlgProperty K H) : HopfIdeal.IsBorel K H.obj ⊥ := by
  apply (HopfIdeal.isBorel_iff_isBorelOverAlgClosed_baseChange K H.obj ⊥).mpr
  rw [CommHopfAlgCat.baseChangeHopfIdeal_bot]
  let H' := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure K) H
  have hsplit : splitTorusCommHopfAlgProperty (AlgebraicClosure K) H' := hH
  exact torus_isBorelOverAlgClosed_bot H' (hsplit.torus _ _)

namespace SplitTorus

variable (K) (ι : Type u) [Finite ι]

/-- The split torus on a finite index type, with itself as maximal torus and Borel subgroup. -/
def groupData : ReductiveGroupData K where
  coordinateAlgebra := DiagonalizableGroup.coordinateRing K (TauCeti.SplitTorus.characterGroup ι)
  torusIndex := ι
  finiteIndex := inferInstance
  torusIdeal := ⊥
  borelIdeal := ⊥
  borel_le_torus := le_rfl
  isMaximalTorus := torus_isMaximalTorus_bot _
    ((TauCeti.SplitTorus.splitTorus_coordinateRing K ι).torus _ _)
  isBorel := torus_isBorel_bot _
    ((TauCeti.SplitTorus.splitTorus_coordinateRing K ι).torus _ _)
  torusSplit := BialgHom.id K _
  split_surjective := Function.surjective_id
  split_eq_zero := by
    intro a
    simp only [BialgHom.id_apply, HopfIdeal.bot_toIdeal, Ideal.mem_bot]
  reductive := (TauCeti.SplitTorus.splitTorus_coordinateRing K ι).reductive

end SplitTorus

namespace ReductiveGroupData

variable (G : ReductiveGroupData K)

private def torusDataSplit : G.torusAlgebra →ₐc[K]
    MonoidAlgebra K (Multiplicative (G.torusIndex →₀ ℤ)) :=
  Bialgebra.Quotient.liftBialgHom G.torusIdeal.toIdeal G.torusSplit
    (fun a ha => (G.split_eq_zero a).mpr ha)

private theorem torusDataSplit_surjective : Function.Surjective G.torusDataSplit := by
  intro y
  obtain ⟨a, ha⟩ := G.split_surjective y
  refine ⟨Ideal.Quotient.mkₐ K G.torusIdeal.toIdeal a, ?_⟩
  change G.torusSplit a = y
  exact ha

private theorem torusDataSplit_eq_zero (a : G.torusAlgebra) :
    G.torusDataSplit a = 0 ↔ a = 0 := by
  refine Quotient.inductionOn' a ?_
  intro a
  change G.torusSplit a = 0 ↔ Ideal.Quotient.mk G.torusIdeal.toIdeal a = 0
  rw [G.split_eq_zero, Ideal.Quotient.eq_zero_iff_mem]

/-- The chosen maximal torus, with itself as maximal torus and Borel subgroup. -/
def torusData : ReductiveGroupData K where
  coordinateAlgebra := G.torusAlgebra
  torusIndex := G.torusIndex
  finiteIndex := G.finiteIndex
  torusIdeal := ⊥
  borelIdeal := ⊥
  borel_le_torus := le_rfl
  isMaximalTorus := torus_isMaximalTorus_bot _ G.torus_isTorus
  isBorel := torus_isBorel_bot _ G.torus_isTorus
  torusSplit := G.torusDataSplit
  split_surjective := G.torusDataSplit_surjective
  split_eq_zero := by
    intro a
    simpa only [HopfIdeal.bot_toIdeal, Ideal.mem_bot] using G.torusDataSplit_eq_zero a
  reductive := G.torus_isTorus.reductive

end ReductiveGroupData

end ReductiveGroups
