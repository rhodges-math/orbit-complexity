import OrbitComplexity.SchubertGeometry.Parabolics.Schubert

/-! # Dense open cells in partial Schubert varieties

Each partial Schubert cell is a dense open subvariety of its reduced closure.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups SchubertGeometry Topology
open TopologicalSpace
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

variable [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- The inclusion of a partial Schubert cell in its Schubert variety. -/
def partialCellInClosure (J : Set G.rootBase.support) (w : G.weylGroup) :
    (partialSchubertCell G J w).toOver ⟶ (partialSchubertVariety G J w).toOver := by
  let i := partialSchubertInclusion G J w
  let f := partialSchubertCellInclusion G J w
  have hr : Set.range f.left ⊆ Set.range i.left := by
    rw [partialSchubertInclusion_range]
    exact subset_closure
  let g := liftPreimmersion (X := (partialFlagVariety G J).scheme)
    (Y := (partialSchubertCell G J w).scheme) (Z := (partialSchubertVariety G J w).scheme)
    i.left f.left hr
  refine Over.homMk g ?_
  change g ≫ (partialSchubertVariety G J w).toSpec = (partialSchubertCell G J w).toSpec
  have hi : i.left ≫ (partialFlagVariety G J).toSpec =
      (partialSchubertVariety G J w).toSpec := i.w
  rw [← hi, ← Category.assoc]
  dsimp only [g]
  rw [liftPreimmersion_fac]
  exact f.w

/-- The cell-to-closure inclusion commutes with the ambient partial flag inclusions. -/
theorem partialCellInClosure_comp (J : Set G.rootBase.support) (w : G.weylGroup) :
    partialCellInClosure G J w ≫ partialSchubertInclusion G J w =
      partialSchubertCellInclusion G J w := by
  apply Over.OverMorphism.ext
  exact liftPreimmersion_fac (X := (partialFlagVariety G J).scheme)
    (Y := (partialSchubertCell G J w).scheme) (Z := (partialSchubertVariety G J w).scheme)
    (partialSchubertInclusion G J w).left (partialSchubertCellInclusion G J w).left
    (by rw [partialSchubertInclusion_range]; exact subset_closure)

/-- A partial Schubert cell is open in its Schubert variety. -/
instance partialCellInClosure_isOpen (J : Set G.rootBase.support) (w : G.weylGroup) :
    IsOpenImmersion (partialCellInClosure G J w).left := by
  apply locallyClosedLift_isOpen (partialFlagVariety G J)
    (Set.range (Variety.orbitMorphism (borelVariety G) (partialFlagVariety G J)
      (partialWeylFlagPoint G J w)).left)
    (orbitImage_locallyClosed (borelVariety G) (partialFlagVariety G J)
      (partialWeylFlagPoint G J w)) (partialSchubertSupport G J w)
  · apply Closeds.ext
    exact congrArg closure (orbitInclusion_range (borelVariety G)
      (partialFlagVariety G J) (partialWeylFlagPoint G J w))
  · exact partialCellInClosure_comp G J w

/-- A partial Schubert cell is dense in its Schubert variety. -/
instance partialCellInClosure_dominant (J : Set G.rootBase.support) (w : G.weylGroup) :
    IsDominant (partialCellInClosure G J w).left := by
  have : Nonempty (partialSchubertCell G J w).toOver.left :=
    inferInstanceAs (Nonempty (partialSchubertCell G J w).scheme)
  have : PreirreducibleSpace (partialSchubertVariety G J w).toOver.left :=
    inferInstanceAs (PreirreducibleSpace (partialSchubertVariety G J w).scheme)
  rw [isDominant_iff]
  exact (partialCellInClosure G J w).left.isOpenEmbedding.2.dense (Set.range_nonempty _)

end SchubertGeometry
