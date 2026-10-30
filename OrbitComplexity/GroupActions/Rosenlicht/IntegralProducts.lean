import OrbitComplexity.GroupActions.Rosenlicht.SchemeProducts
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Integral products over an algebraically closed field

Affine pullback charts are integral. They give reducedness of a general product.
A dense affine open of the first factor pulls back densely along the open
projection; its irreducibility gives irreducibility of the whole product.

## Main results

* `isIntegral_pullback_over_field`: integrality of products over an algebraically closed field.
-/

namespace GroupActions

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
variable (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType f]

private lemma reduced_pullback : IsReduced (pullback f g) := by
  let p : (pullback f g : Scheme) ⟶ X := pullback.fst f g
  rw [IsReduced.iff_of_openCover _ (X.affineCover.pullback₁ p)]
  intro i
  have : IsOpenImmersion (X.affineCover.f i) := X.affineCover.map_prop i
  have : IsAffine (X.affineCover.X i) := Scheme.isAffine_affineCover X i
  by_cases hne : Nonempty (X.affineCover.X i)
  · have : IsIntegral (X.affineCover.X i) :=
      isIntegral_of_isOpenImmersion (X.affineCover.f i)
    have : IsIntegral (pullback (X.affineCover.f i ≫ f) g) :=
      isIntegral_pullback_of_isAffine (X.affineCover.f i ≫ f) g
    let e : (X.affineCover.pullback₁ p).X i ≅ pullback (X.affineCover.f i ≫ f) g :=
      pullbackSymmetry p (X.affineCover.f i) ≪≫
      pullbackRightPullbackFstIso f g (X.affineCover.f i)
    exact isReduced_of_isOpenImmersion e.hom
  · have : IsEmpty ((X.affineCover.pullback₁ p).X i) :=
      ⟨fun x ↦ hne ⟨pullback.snd p (X.affineCover.f i) x⟩⟩
    have (x : (X.affineCover.pullback₁ p).X i) :
        _root_.IsReduced (((X.affineCover.pullback₁ p).X i).presheaf.stalk x) := isEmptyElim x
    exact isReduced_of_isReduced_stalk _

private lemma irreducible_pullback : IrreducibleSpace (pullback f g : Scheme) := by
  obtain ⟨U, hUa, hU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := genericPoint X) (by trivial)
  have : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  have : IsAffine U.toScheme := hUa
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : IsIntegral (pullback (U.ι ≫ f) g) :=
    isIntegral_pullback_of_isAffine (U.ι ≫ f) g
  let p : (pullback f g : Scheme) ⟶ X := pullback.fst f g
  let Q := pullback U.ι p
  let e := pullbackRightPullbackFstIso f g U.ι
  have : IsIntegral Q := IsIntegral.of_isIso e.inv
  let j : Q ⟶ pullback f g := pullback.snd U.ι p
  have hdU : Dense (U : Set X) := U.isOpen.dense ⟨genericPoint X, hU⟩
  have hd : Dense (Set.range j) := by
    rw [Scheme.Pullback.range_snd]
    have hd' : Dense (Set.range U.ι) := by simpa only [Scheme.Opens.range_ι] using hdU
    exact hd'.preimage p.isOpenMap
  have hi : IsIrreducible (Set.range j) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ Q).image j j.continuous.continuousOn
  apply (irreducibleSpace_def (pullback f g : Scheme)).mpr
  change IsIrreducible (Set.univ : Set (pullback f g : Scheme))
  rw [← hd.closure_eq]
  exact hi.closure

/-- Over an algebraically closed field, the product of an integral scheme locally
of finite type with an integral locally noetherian scheme is integral. -/
theorem isIntegral_pullback_over_field : IsIntegral (pullback f g) := by
  have : IsReduced (pullback f g) := reduced_pullback f g
  have : IrreducibleSpace (pullback f g : Scheme) := irreducible_pullback f g
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

end GroupActions
