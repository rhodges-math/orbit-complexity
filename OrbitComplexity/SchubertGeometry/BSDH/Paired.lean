import OrbitComplexity.SchubertGeometry.BSDH.Opposite
import OrbitComplexity.SchubertGeometry.FlagVariety.Transversality
import OrbitComplexity.FrobeniusSplitting.Normality.FlatDescent
import OrbitComplexity.FrobeniusSplitting.Normality.Smooth

/-! # Normal stalks of paired BSDH sources

The transverse flag action gives a smooth cover after pullback along the
two endpoints. Untwisting identifies it with a Borel-product cover of the raw
endpoint intersection. Flat surjective descent then gives normal domain stalks.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
universe u

section Schemes
variable {K : Type u} [Field K]

private theorem product_smooth (X Y : Over (Spec (CommRingCat.of K)))
    [Smooth X.hom] [Smooth Y.hom] : Smooth (X ⊗ Y).hom := by
  change Smooth (pullback.fst X.hom Y.hom ≫ X.hom)
  infer_instance

private theorem transverseCover_smooth (B O F X Y : Over (Spec (CommRingCat.of K)))
    [GrpObj B] [GrpObj O] [ModObj B F] [ModObj O F] [ModObj B X] [ModObj O Y]
    (f : X ⟶ F) (g : Y ⟶ F) [IsModHom B f] [IsModHom O g]
    [Smooth X.hom] [Smooth Y.hom] [Smooth (transverseAction B O F).left] :
    Smooth ((B ⊗ O) ⊗ pullback f g).hom := by
  let p := transverseAction B O F
  let k := f ⊗ₘ g
  have hp : IsPullback (pullback.fst p k).left (pullback.snd p k).left p.left k.left :=
    (IsPullback.of_hasPullback p k).map (Over.forget (Spec (CommRingCat.of K)))
  have hs : Smooth (pullback.snd p k).left :=
    MorphismProperty.of_isPullback hp inferInstance
  have : Smooth (X ⊗ Y).hom := product_smooth X Y
  have hq : Smooth (pullback p k).hom := by
    rw [← (pullback.snd p k).w]
    infer_instance
  let e := equivariantIntersectionIso B O F f g
  rw [← e.hom.w]
  infer_instance

private theorem product_stalks_descent (H Z : Over (Spec (CommRingCat.of K)))
    [MonObj H] [Smooth H.hom] [Smooth (H ⊗ Z).hom] :
    ∀ z : Z.left, IsDomain (Z.left.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.left.presheaf.stalk z) := by
  have : Flat (snd H Z).left := by
    change Flat (pullback.snd H.hom Z.hom)
    infer_instance
  let s : Z ⟶ H ⊗ Z := lift 1 (𝟙 Z)
  have hs : s ≫ snd H Z = 𝟙 Z := by simp [s]
  have : Surjective (snd H Z).left := ⟨by
    intro z
    refine ⟨s.left z, ?_⟩
    exact congrArg (fun m : Z ⟶ Z => m.left z) hs⟩
  exact FrobeniusSplitting.stalks_of_flat_surjective (snd H Z).left
    (FrobeniusSplitting.stalks_of_smooth (H ⊗ Z).hom)

end Schemes

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The raw fibre product of the ordinary and longest-translated BSDH endpoints. -/
abbrev pairedBSDHSource (a b : List G.rootBase.support) :
    Over (Spec (CommRingCat.of K)) :=
  pullback (Over.homMk (bsdhMap G a) rfl :
    (bsdhVariety G a).toOver ⟶ (flagVariety G).toOver) (bsdhOppositeEndpoint G b)

private theorem pairedCover_smooth (a b : List G.rootBase.support) :
    Smooth (((borelVariety G).toOver ⊗ (oppositeBorelVariety G).toOver) ⊗
      pairedBSDHSource G a b).hom := by
  let := bsdhBorelAction G a
  let := bsdhOppositeAction G b
  have := bsdhBorelEquivariant G a
  have := bsdhOppositeEquivariant G b
  have : Smooth (bsdhVariety G a).toOver.hom := bsdh_smooth G a
  have : Smooth (bsdhVariety G b).toOver.hom := bsdh_smooth G b
  have : Smooth (transverseAction (borelVariety G).toOver
      (oppositeBorelVariety G).toOver (flagVariety G).toOver).left :=
    flagTransverseAction_smooth G
  exact transverseCover_smooth (borelVariety G).toOver (oppositeBorelVariety G).toOver
    (flagVariety G).toOver (bsdhVariety G a).toOver (bsdhVariety G b).toOver
    (Over.homMk (bsdhMap G a) rfl) (bsdhOppositeEndpoint G b)

/-- The paired endpoint source has normal domain stalks, without a reducedness premise. -/
theorem pairedBSDHSource_stalks (a b : List G.rootBase.support) :
    ∀ z : (pairedBSDHSource G a b).left,
      IsDomain ((pairedBSDHSource G a b).left.presheaf.stalk z) ∧
        IsIntegrallyClosed ((pairedBSDHSource G a b).left.presheaf.stalk z) := by
  have : Smooth (borelVariety G).toOver.hom := by
    change Smooth (borelVariety G).toSpec
    exact TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced _
  have : Smooth (oppositeBorelVariety G).toOver.hom := by
    change Smooth (oppositeBorelVariety G).toSpec
    exact TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced _
  have : Smooth ((borelVariety G).toOver ⊗ (oppositeBorelVariety G).toOver).hom :=
    product_smooth (borelVariety G).toOver (oppositeBorelVariety G).toOver
  have := pairedCover_smooth G a b
  exact product_stalks_descent
    ((borelVariety G).toOver ⊗ (oppositeBorelVariety G).toOver) (pairedBSDHSource G a b)

/-- The raw paired endpoint fibre product is reduced as a consequence of its stalks. -/
instance pairedBSDHSource_reduced (a b : List G.rootBase.support) :
    IsReduced (pairedBSDHSource G a b).left := by
  have (z : (pairedBSDHSource G a b).left) :
      IsDomain ((pairedBSDHSource G a b).left.presheaf.stalk z) :=
    (pairedBSDHSource_stalks G a b z).1
  exact isReduced_of_isReduced_stalk _

end
end SchubertGeometry
