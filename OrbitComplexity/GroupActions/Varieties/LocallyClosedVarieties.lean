import OrbitComplexity.GroupActions.Varieties.Subvarieties
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties

/-! # Locally closed subvarieties

A locally closed subset is open in its closure. Giving the closure its reduced induced
scheme structure and restricting to this open subset constructs the induced subvariety.

## Main definitions

* `GroupActions.Variety.locallyClosedSubvariety`: the induced variety on a locally closed set.
* `GroupActions.Variety.locallyClosedInclusion`: its inclusion into the ambient variety.

## Main results

* `GroupActions.Variety.locallyClosedInclusion_range`: the inclusion has the prescribed image.
* `GroupActions.Variety.locallyClosedSubvariety_dim`: an irreducible locally closed
  subvariety has the dimension of its closure.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (X : GroupActions.Variety K)

private def closureSubvariety (S : Set X.scheme) : GroupActions.Variety K :=
  X.closedSubvariety ⟨closure S, isClosed_closure⟩

private def closureInclusion (S : Set X.scheme) : (closureSubvariety X S).toOver ⟶ X.toOver :=
  X.closedInclusion ⟨closure S, isClosed_closure⟩

private theorem exists_ambientOpen {S : Set X.scheme} (hS : IsLocallyClosed S) :
    ∃ U : Set X.scheme, IsOpen U ∧ S = U ∩ closure S :=
  ((isLocallyClosed_tfae S).out 1 5).mp hS

private def ambientOpen {S : Set X.scheme} (hS : IsLocallyClosed S) : X.scheme.Opens :=
  ⟨Classical.choose (exists_ambientOpen X hS),
    (Classical.choose_spec (exists_ambientOpen X hS)).1⟩

private theorem ambientOpen_inter {S : Set X.scheme} (hS : IsLocallyClosed S) :
    S = (ambientOpen X hS : Set X.scheme) ∩ closure S :=
  (Classical.choose_spec (exists_ambientOpen X hS)).2

/-- The reduced induced variety structure on a locally closed subset. -/
def locallyClosedSubvariety (S : Set X.scheme) (hS : IsLocallyClosed S) :
    GroupActions.Variety K :=
  (closureSubvariety X S).openSubvariety
    ((closureInclusion X S).left ⁻¹ᵁ ambientOpen X hS)

/-- The inclusion of a locally closed subvariety is a morphism over the base field. -/
def locallyClosedInclusion (S : Set X.scheme) (hS : IsLocallyClosed S) :
    (X.locallyClosedSubvariety S hS).toOver ⟶ X.toOver :=
  (closureSubvariety X S).openInclusion
    ((closureInclusion X S).left ⁻¹ᵁ ambientOpen X hS) ≫ closureInclusion X S

/-- The image of the locally closed subvariety's inclusion is the prescribed subset. -/
theorem locallyClosedInclusion_range (S : Set X.scheme) (hS : IsLocallyClosed S) :
    Set.range ((X.locallyClosedInclusion S hS).left :
      (X.locallyClosedSubvariety S hS).scheme → X.scheme) = S := by
  let f := closureInclusion X S
  change Set.range (f.left ∘ ((closureSubvariety X S).openInclusion
    (f.left ⁻¹ᵁ ambientOpen X hS)).left) = S
  rw [Set.range_comp, openInclusion_range]
  change f.left '' (f.left ⁻¹' (ambientOpen X hS : Set X.scheme)) = S
  rw [Set.image_preimage_eq_inter_range]
  have hf : Set.range (f.left : (closureSubvariety X S).scheme → X.scheme) = closure S :=
    X.closedInclusion_range ⟨closure S, isClosed_closure⟩
  rw [hf, ← ambientOpen_inter X hS]

/-- The inclusion of a locally closed subvariety is a preimmersion. -/
instance locallyClosedInclusion_isPreimmersion (S : Set X.scheme) (hS : IsLocallyClosed S) :
    IsPreimmersion (X.locallyClosedInclusion S hS).left := by
  have : IsClosedImmersion (closureInclusion X S).left :=
    inferInstanceAs (IsClosedImmersion
      (X.closedInclusion ⟨closure S, isClosed_closure⟩).left)
  exact inferInstanceAs (IsPreimmersion (((closureSubvariety X S).openInclusion
    ((closureInclusion X S).left ⁻¹ᵁ ambientOpen X hS)).left ≫ (closureInclusion X S).left))

/-- The locally closed subvariety has the topology induced on the prescribed subset. -/
def locallyClosedHomeomorph (S : Set X.scheme) (hS : IsLocallyClosed S) :
    (X.locallyClosedSubvariety S hS).scheme ≃ₜ S :=
  (X.locallyClosedInclusion S hS).left.isEmbedding.toHomeomorph.trans
    (.setCongr (X.locallyClosedInclusion_range S hS))

/-- An irreducible locally closed subvariety has the dimension of its closure. -/
theorem locallyClosedSubvariety_dim (S : Set X.scheme) (hS : IsLocallyClosed S)
    (hirr : IsIrreducible S) :
    (X.locallyClosedSubvariety S hS).dim = topologicalKrullDim (closure S) := by
  have hdim :=
    TauCeti.AlgebraicGeometry.topologicalKrullDim_inter_eq_of_locallyOfFiniteType X.toSpec
      hirr.closure isClosed_closure (ambientOpen X hS).isOpen
      (show (closure S ∩ (ambientOpen X hS : Set X.scheme)).Nonempty by
        rw [Set.inter_comm, ← ambientOpen_inter X hS]
        exact hirr.nonempty)
  rw [Set.inter_comm, ← ambientOpen_inter X hS] at hdim
  exact (X.locallyClosedHomeomorph S hS).isHomeomorph.topologicalKrullDim_eq.trans hdim

end

end GroupActions.Variety
