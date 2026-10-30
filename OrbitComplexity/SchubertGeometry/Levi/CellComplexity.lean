import OrbitComplexity.SchubertGeometry.Levi.BorelComparison
import OrbitComplexity.SchubertGeometry.Cells.SchubertClosure
import OrbitComplexity.GroupActions.Rosenlicht.OpenComplexity
/-! # Complexity on the open Schubert cell

The top Schubert cell includes as a dense open subvariety of its reduced closure.
For an equivariant Levi action, restricting to the Levi Borel and this dense open
preserves minimum orbit codimension.
-/

open CategoryTheory AlgebraicGeometry GroupActions Topology TopologicalSpace
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K]
private def locallyClosedToClosure (X : Variety K) (S : Set X.scheme)
    (hS : IsLocallyClosed S) :
    (X.locallyClosedSubvariety S hS).toOver ⟶
      (X.closedSubvariety ⟨closure S, isClosed_closure⟩).toOver :=
  Variety.openInclusion _ _
private theorem locallyClosedToClosure_fac (X : Variety K) (S : Set X.scheme)
    (hS : IsLocallyClosed S) :
    locallyClosedToClosure X S hS ≫ X.closedInclusion ⟨closure S, isClosed_closure⟩ =
      X.locallyClosedInclusion S hS := rfl
private theorem locallyClosedLift_isOpen (X : Variety K) (S : Set X.scheme)
    (hS : IsLocallyClosed S) (Z : Closeds X.scheme)
    (hZ : Z = ⟨closure S, isClosed_closure⟩)
    (f : (X.locallyClosedSubvariety S hS).toOver ⟶ (X.closedSubvariety Z).toOver)
    (hf : f ≫ X.closedInclusion Z = X.locallyClosedInclusion S hS) :
    IsOpenImmersion f.left := by
  subst Z
  have he : f = locallyClosedToClosure X S hS := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (X.closedInclusion ⟨closure S, isClosed_closure⟩).left).mp
    exact congrArg Over.Hom.left (hf.trans (locallyClosedToClosure_fac X S hS).symm)
  rw [he]
  exact Variety.openInclusion_isOpenImmersion _ _
open ReductiveGroups
variable [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
/-- The top Schubert cell includes as an open subvariety of its Schubert variety. -/
instance schubertCellOfLE_self_isOpen (w : G.weylGroup) :
    IsOpenImmersion (schubertCellOfLE G w w (WeylBruhatLE.refl G.rootBase w)).left := by
  apply locallyClosedLift_isOpen (flagVariety G)
    (Set.range (Variety.orbitMorphism (borelVariety G) (flagVariety G)
      (weylFlagPoint G w)).left)
    (orbitImage_locallyClosed (borelVariety G) (flagVariety G) (weylFlagPoint G w))
    (schubertSupport G w)
  · apply Closeds.ext
    exact congrArg closure (orbitInclusion_range (borelVariety G)
      (flagVariety G) (weylFlagPoint G w))
  · exact schubertCellOfLE_comp G w w _
/-- The top-cell inclusion has dense image in the Schubert variety. -/
instance schubertCellOfLE_self_isDominant (w : G.weylGroup) :
    IsDominant (schubertCellOfLE G w w (WeylBruhatLE.refl G.rootBase w)).left := by
  rw [isDominant_iff]
  exact (schubertCellOfLE G w w (WeylBruhatLE.refl G.rootBase w)).left.isOpenEmbedding.2.dense
    (Set.range_nonempty _)
/-- Levi complexity is the minimum Levi--Borel orbit codimension on the open Schubert cell. -/
theorem levi_schubert_complexity_cell (I : Set G.rootBase.support) (w : G.weylGroup)
    [ModObj (leviVariety G I).toOver (schubertVariety G w).toOver]
    [IsModHom (leviVariety G I).toOver (schubertInclusion G w)] :
    letI : ModObj (reductiveVariety (leviGroupData G I)).toOver
        (schubertVariety G w).toOver :=
      inferInstanceAs (ModObj (leviVariety G I).toOver (schubertVariety G w).toOver)
    complexity (leviGroupData G I) (schubertVariety G w) =
      minOrbitCodim (leviBorelVariety G I) (schubertCell G w) := by
  apply (levi_schubert_complexity G I w).trans
  exact (Variety.minOrbitCodim_eq_of_openImmersion (leviBorelVariety G I)
    (schubertCell G w) (schubertVariety G w)
    (schubertCellOfLE G w w (WeylBruhatLE.refl G.rootBase w))).symm
end SchubertGeometry
