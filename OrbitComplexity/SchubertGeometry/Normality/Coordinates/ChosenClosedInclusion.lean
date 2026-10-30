import OrbitComplexity.SchubertGeometry.Connectedness.PrefixCommonCoefficients
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Closed flag targets and the prescribed inclusion

The coordinate quotient construction applies to arbitrary closed flag
supports. Its coefficient targets retain their comparison with the chosen
flag model. An isomorphism retained together with its ambient triangle then
transfers a closed immersion to a prescribed scalar inclusion.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting ReductiveGroups
open scoped TensorProduct

namespace SchubertGeometry

universe u

open private common_targets common_from_diagram
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixCommonCoefficients
open private retain_surjective_family
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixClosedTargets
open private variety_diagonal
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets
open private scalar_closed
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing

private theorem closed_of_iso_triangle {X Y Z : Scheme.{u}}
    (E : X ≅ Y) (i : Y ⟶ Z) (j : X ⟶ Z) [IsClosedImmersion i]
    (h : E.hom ≫ i = j) : IsClosedImmersion j := by
  rw [← h]
  infer_instance

private theorem scalar_tower_triangle {B T V : Scheme.{u}}
    (κ : T ⟶ B) (ρ : V ⟶ T) {X Y : Over B} (j : X ⟶ Y) :
    (chosenScalarArrow ρ (chosenScalarArrow κ j)).left ≫
        (pullbackRightPullbackFstIso κ Y.hom ρ).hom =
      (pullbackRightPullbackFstIso κ X.hom ρ).hom ≫
        (chosenScalarArrow (ρ ≫ κ) j).left := by
  let EX := pullbackRightPullbackFstIso κ X.hom ρ
  let EY := pullbackRightPullbackFstIso κ Y.hom ρ
  let jκ := chosenScalarArrow κ j
  let jρ := chosenScalarArrow ρ jκ
  let jζ := chosenScalarArrow (ρ ≫ κ) j
  have hjζ : jζ.left ≫ pullback.fst (ρ ≫ κ) Y.hom =
      pullback.fst (ρ ≫ κ) X.hom := jζ.w
  have hjρ : jρ.left ≫ pullback.snd ρ (pullback.fst κ Y.hom) =
      pullback.snd ρ (pullback.fst κ X.hom) ≫ jκ.left :=
    chosenScalarArrow_snd ρ jκ
  have hjκ : jκ.left ≫ pullback.snd κ Y.hom =
      pullback.snd κ X.hom ≫ j.left := chosenScalarArrow_snd κ j
  have hEXf : EX.hom ≫ pullback.fst (ρ ≫ κ) X.hom =
      pullback.fst ρ (pullback.fst κ X.hom) :=
    pullbackRightPullbackFstIso_hom_fst κ X.hom ρ
  have hEYf : EY.hom ≫ pullback.fst (ρ ≫ κ) Y.hom =
      pullback.fst ρ (pullback.fst κ Y.hom) :=
    pullbackRightPullbackFstIso_hom_fst κ Y.hom ρ
  have hEXs : EX.hom ≫ pullback.snd (ρ ≫ κ) X.hom =
      pullback.snd ρ (pullback.fst κ X.hom) ≫ pullback.snd κ X.hom :=
    pullbackRightPullbackFstIso_hom_snd κ X.hom ρ
  have hEYs : EY.hom ≫ pullback.snd (ρ ≫ κ) Y.hom =
      pullback.snd ρ (pullback.fst κ Y.hom) ≫ pullback.snd κ Y.hom :=
    pullbackRightPullbackFstIso_hom_snd κ Y.hom ρ
  change jρ.left ≫ EY.hom = EX.hom ≫ jζ.left
  apply pullback.hom_ext
  · calc
      (jρ.left ≫ EY.hom) ≫ pullback.fst (ρ ≫ κ) Y.hom =
          jρ.left ≫ pullback.fst ρ (pullback.fst κ Y.hom) := by
        rw [Category.assoc, hEYf]
      _ = pullback.fst ρ (pullback.fst κ X.hom) := jρ.w
      _ = EX.hom ≫ pullback.fst (ρ ≫ κ) X.hom := hEXf.symm
      _ = (EX.hom ≫ jζ.left) ≫ pullback.fst (ρ ≫ κ) Y.hom := by
        rw [Category.assoc, hjζ]
  · calc
      (jρ.left ≫ EY.hom) ≫ pullback.snd (ρ ≫ κ) Y.hom =
          jρ.left ≫ (pullback.snd ρ (pullback.fst κ Y.hom) ≫
            pullback.snd κ Y.hom) := by rw [Category.assoc, hEYs]
      _ = (pullback.snd ρ (pullback.fst κ X.hom) ≫ jκ.left) ≫
          pullback.snd κ Y.hom := by
        rw [← Category.assoc, hjρ]
      _ = pullback.snd ρ (pullback.fst κ X.hom) ≫
          (pullback.snd κ X.hom ≫ j.left) := by
        rw [Category.assoc, hjκ]
      _ = (EX.hom ≫ pullback.snd (ρ ≫ κ) X.hom) ≫ j.left := by
        rw [hEXs, Category.assoc]
      _ = EX.hom ≫ (pullback.snd (ρ ≫ κ) X.hom ≫ j.left) :=
        Category.assoc _ _ _
      _ = EX.hom ≫ (jζ.left ≫ pullback.snd (ρ ≫ κ) Y.hom) :=
        congrArg (fun m => EX.hom ≫ m) (chosenScalarArrow_snd (ρ ≫ κ) j).symm
      _ = (EX.hom ≫ jζ.left) ≫ pullback.snd (ρ ≫ κ) Y.hom :=
        (Category.assoc _ _ _).symm

/-- Closed immersion of an iterated scalar inclusion gives closed immersion
of the induced inclusion for the composite scalar map. -/
theorem closed_scalar_tower {B T V : Scheme.{u}}
    (κ : T ⟶ B) (ρ : V ⟶ T) {X Y : Over B} (j : X ⟶ Y)
    [IsClosedImmersion (chosenScalarArrow ρ (chosenScalarArrow κ j)).left] :
    IsClosedImmersion (chosenScalarArrow (ρ ≫ κ) j).left := by
  let EX := pullbackRightPullbackFstIso κ X.hom ρ
  let EY := pullbackRightPullbackFstIso κ Y.hom ρ
  let jρ := (chosenScalarArrow ρ (chosenScalarArrow κ j)).left
  let jζ := (chosenScalarArrow (ρ ≫ κ) j).left
  have htriangle : jρ ≫ EY.hom = EX.hom ≫ jζ :=
    scalar_tower_triangle κ ρ j
  have hcomp : EX.inv ≫ (jρ ≫ EY.hom) = jζ := by
    rw [htriangle, ← Category.assoc, EX.inv_hom_id, Category.id_comp]
  have hclosed : IsClosedImmersion (EX.inv ≫ (jρ ≫ EY.hom)) := by
    let : IsClosedImmersion jρ := inferInstanceAs
      (IsClosedImmersion (chosenScalarArrow ρ (chosenScalarArrow κ j)).left)
    infer_instance
  change IsClosedImmersion jζ
  rw [← hcomp]
  exact hclosed

/-- Finite quotient coefficients and Cartesian overlaps construct closed
targets for arbitrary closed flag supports over an extension of the chosen
flag model. The scalar comparisons retain both original projections. -/
theorem exists_closed_flag_common
    {K J I : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Finite J] [Finite I]
    (G : ReductiveGroupData K)
    (Z : I → TopologicalSpace.Closeds (flagVariety G).scheme)
    (U : J → (flagVariety G).scheme.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (hcover : (⨆ t, U t) = ⊤)
    (S₀ : Subalgebra ℤ K) (hS₀ : S₀.FG) (P : Over (Spec (.of S₀)))
    [CompactSpace P.left] [LocallyOfFinitePresentation P.hom]
    (qF : (flagVariety G).scheme ⟶ P.left)
    (hF : IsPullback qF (flagVariety G).toSpec P.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
    (start₀ : CoefficientStage S₀) :
    let X := fun i => ((flagVariety G).closedSubvariety (Z i)).scheme
    let j : ∀ i, X i ⟶ (flagVariety G).scheme :=
      fun i => ((flagVariety G).closedInclusion (Z i)).left
    let _ : IsAffineHom (pullback.diagonal (terminal.from (flagVariety G).scheme)) :=
      variety_diagonal (flagVariety G)
    let _ (i : I) : IsAffineHom (pullback.diagonal (terminal.from (X i))) :=
      variety_diagonal ((flagVariety G).closedSubvariety (Z i))
    common_targets X j (flagVariety G).toSpec U hU S₀ P qF start₀ := by
  let X := fun i => ((flagVariety G).closedSubvariety (Z i)).scheme
  let j : ∀ i, X i ⟶ (flagVariety G).scheme :=
    fun i => ((flagVariety G).closedInclusion (Z i)).left
  let : IsAffineHom (pullback.diagonal (terminal.from (flagVariety G).scheme)) :=
    variety_diagonal (flagVariety G)
  let (i : I) : IsAffineHom (pullback.diagonal (terminal.from (X i))) :=
    variety_diagonal ((flagVariety G).closedSubvariety (Z i))
  obtain ⟨S, N, e, β, hS, hfp, _hsm, hn, _hinj, hβ, hsurj, hopen, hpush⟩ :=
    exists_closed_flag_models G Z U hU
  let C := {s : Finset J // s.Nonempty}
  let H : (Σ _ : I, C) ⥤ C :=
    Sigma.desc (fun _ => intersectionIndexMap (id : J → J))
  let (x : (Σ _ : I, C) ⊕ C) : Algebra.FinitePresentation S (N.obj x) := hfp x
  obtain ⟨R, hSR, hR⟩ := retain_surjective_family S hS
    (fun x : Σ _ : I, C => N.obj (.inr (H.obj x)))
    (fun x => N.obj (.inl x)) (fun x => (β.app x).hom) hsurj
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  exact common_from_diagram X j (flagVariety G).toSpec U hU hcover
    S₀ hS₀ P qF hF start₀ S N e β hfp hn hβ hopen hpush R hSR hR.1 hR.2

/-- A closed model in the same ambient scheme transfers to the induced
scalar inclusion of the prescribed target. Both inverse comparisons and
the ambient triangle are retained at one coefficient stage. -/
theorem exists_retained_closed_inclusion {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    (D P F : Over (Spec (.of S)))
    [CompactSpace D.left] [QuasiSeparatedSpace D.left]
    [CompactSpace P.left] [QuasiSeparatedSpace P.left]
    [LocallyOfFinitePresentation D.hom] [LocallyOfFinitePresentation P.hom]
    [LocallyOfFiniteType F.hom]
    {N Q : Scheme.{u}} (n : N ⟶ Spec (.of K))
    (qD : N ⟶ D.left) (qP : N ⟶ P.left)
    (hD : IsPullback qD n D.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hP : IsPullback qP n P.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (j : D ⟶ F) (i : P ⟶ F) [IsClosedImmersion i.left]
    (jN : N ⟶ Q) (qF : Q ⟶ F.left)
    (hj : qD ≫ j.left = jN ≫ qF) (hi : qP ≫ i.left = jN ≫ qF)
    (start : CoefficientStage S) :
    let E := chosenPairIso (Spec.map (CommRingCat.ofHom (algebraMap S K)))
      D P n qD qP hD hP
    ∃ (k : CoefficientStage S) (_ : start ≤ k)
      (E₀ : stageScalarModel S D.hom k ≅ stageScalarModel S P.hom k),
      ((modelScalarCone S D.hom).π.app (op k) ≫ E₀.hom.left =
        E.hom.left ≫ (modelScalarCone S P.hom).π.app (op k)) ∧
      ((modelScalarCone S P.hom).π.app (op k) ≫ E₀.inv.left =
        E.inv.left ≫ (modelScalarCone S D.hom).π.app (op k)) ∧
      (E₀.hom ≫ chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) i =
        chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) j) ∧
      IsClosedImmersion (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) j).left := by
  dsimp only
  obtain ⟨k, hstart, E₀, hhom, hinv, htriangle⟩ :=
    exists_chosen_paired_retention S hS D P F n qD qP hD hP j i jN qF hj hi start
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  have hiK : IsClosedImmersion (chosenScalarArrow κ i).left := scalar_closed κ i
  let : IsClosedImmersion (chosenScalarArrow κ i).left := hiK
  have hleft : E₀.hom.left ≫ (chosenScalarArrow κ i).left =
      (chosenScalarArrow κ j).left := congrArg (fun f => f.left) htriangle
  have hjK : IsClosedImmersion (chosenScalarArrow κ j).left :=
    @closed_of_iso_triangle _ _ _ ((Over.forget _).mapIso E₀)
      (chosenScalarArrow κ i).left (chosenScalarArrow κ j).left hiK hleft
  exact ⟨k, hstart, E₀, hhom, hinv, htriangle, hjK⟩

end SchubertGeometry
