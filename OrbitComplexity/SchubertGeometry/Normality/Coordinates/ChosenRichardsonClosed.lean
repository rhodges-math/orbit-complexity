import OrbitComplexity.SchubertGeometry.Normality.Coordinates.ChosenClosedInclusion
import OrbitComplexity.SchubertGeometry.Cells.Richardson
import Mathlib.AlgebraicGeometry.Cover.Open
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Closedness on the prescribed Richardson model

The quotient atlas constructs a closed target. Its ambient comparison is
flattened to the prescribed scalar flag model, and its target comparison is
retained with its inverse and ambient triangle. The resulting closed map is
the scalar extension of the chosen inclusion on the chosen target.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open FrobeniusSplitting ReductiveGroups
open scoped TensorProduct

namespace SchubertGeometry

universe u

open private common_targets
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixCommonCoefficients
open private coefficient_targets
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixStageCoordinates
open private target_result stage_properties closed_comp_iso
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixTargetGluing
open private scalar_flag coefficient_triangle
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixScalarCoordinates
open private scalar_functor
  from OrbitComplexity.SchubertGeometry.Connectedness.AppendCellConnected
open private scalar_comparison
  from OrbitComplexity.SchubertGeometry.Connectedness.EmptyEndpointStage
open private variety_diagonal
  from OrbitComplexity.SchubertGeometry.Connectedness.PrefixCoordinateTargets

/-- Commuting squares identify inverse images of open subsets. -/
theorem endpoint_preimage_eq {X₀ Y₀ X Y : Scheme.{u}}
    (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y) (qX : X ⟶ X₀) (qY : Y ⟶ Y₀)
    (h : qX ≫ f₀ = f ≫ qY) (W : Y₀.Opens) :
    qX ⁻¹ᵁ (f₀ ⁻¹ᵁ W) = f ⁻¹ᵁ (qY ⁻¹ᵁ W) := by
  ext z
  change f₀ (qX z) ∈ W ↔ qY (f z) ∈ W
  have hz : f₀ (qX z) = qY (f z) := congrArg (fun g => g z) h
  rw [hz]

/-- Restricting a Cartesian scalar square to matching open sets preserves it. -/
theorem restriction_scalar_square
    {B T X₀ X : Scheme.{u}} (ρ : T ⟶ B)
    (x₀ : X₀ ⟶ B) (x : X ⟶ T) (q : X ⟶ X₀)
    (hq : IsPullback q x x₀ ρ)
    (U : X₀.Opens) (V : X.Opens) (hV : V = q ⁻¹ᵁ U) :
    IsPullback (q.resLE U V (le_of_eq hV))
      (V.ι ≫ x) (U.ι ≫ x₀) ρ := by
  have hpatch : IsPullback (q.resLE U V (le_of_eq hV)) V.ι U.ι q := by
    apply IsOpenImmersion.isPullback
    · exact (Scheme.Hom.resLE_comp_ι _ _).symm
    · simpa only [Scheme.Opens.opensRange_ι] using hV.symm
  exact hpatch.paste_vert hq

private theorem comp_projection {A B C E : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (p : C ⟶ E) (q : B ⟶ E) (r : A ⟶ E)
    (hg : g ≫ p = q) (hf : f ≫ q = r) : (f ≫ g) ≫ p = r := by
  exact (Category.assoc f g p).trans ((congrArg (fun a => f ≫ a) hg).trans hf)

private theorem comp_projection_pair {A B C E F : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (p : C ⟶ F)
    (q : B ⟶ E) (r : A ⟶ E) (s : E ⟶ F)
    (hg : g ≫ p = q ≫ s) (hf : f ≫ q = r) :
    (f ≫ g) ≫ p = r ≫ s := by
  exact (Category.assoc f g p).trans
    ((congrArg (fun a => f ≫ a) hg).trans
      ((Category.assoc f q s).symm.trans (congrArg (fun a => a ≫ s) hf)))

private theorem postcompose_triangle {A B C D E : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (j : A ⟶ E)
    (q : E ⟶ C) (r : E ⟶ D) (hg : f ≫ g = j ≫ q) (hq : q ≫ h = r) :
    f ≫ (g ≫ h) = j ≫ r := by
  exact (Category.assoc f g h).symm.trans
    ((congrArg (fun a => a ≫ h) hg).trans
      ((Category.assoc j q h).trans (congrArg (fun a => j ≫ a) hq)))

private theorem successive_projections {A B C D : Scheme.{u}}
    (f : A ⟶ B) (p : B ⟶ C) (q : C ⟶ D) (r : A ⟶ C) (t : A ⟶ D)
    (hf : f ≫ p = r) (hr : r ≫ q = t) : f ≫ (p ≫ q) = t := by
  exact (Category.assoc f p q).symm.trans
    ((congrArg (fun a => a ≫ q) hf).trans hr)

private theorem pullback_right_eq {X Y Z S : Scheme.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (h h' : Y ⟶ S) (i : Z ⟶ S)
    (e : h' = h) (H : IsPullback f g h i) : IsPullback f g h' i := by
  rw [e]
  exact H

private theorem closed_from_common_targets
    {Y : Scheme.{u}} {J I K : Type u} [CommRing K]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (X : I → Scheme.{u}) [∀ i, IsAffineHom (pullback.diagonal (terminal.from (X i)))]
    (j : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (j i)]
    (base : Y ⟶ Spec (.of K)) (U : J → Y.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (S₀ : Subalgebra ℤ K) (hS₀ : S₀.FG)
    (D F : Over (Spec (.of S₀)))
    [CompactSpace D.left] [LocallyOfFinitePresentation D.hom]
    [CompactSpace F.left] [LocallyOfFinitePresentation F.hom]
    (i : I) (qD : X i ⟶ D.left) (qF : Y ⟶ F.left)
    (hD : IsPullback qD (j i ≫ base) D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
    (hF : IsPullback qF base F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S₀ K))))
    (d : D ⟶ F) (hd : qD ≫ d.left = j i ≫ qF)
    (start₀ : CoefficientStage S₀)
    (h : common_targets X j base U hU S₀ F qF start₀) :
    ∃ (r : CoefficientStage S₀) (_ : start₀ ≤ r),
      IsClosedImmersion (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom)) d).left := by
  dsimp only [common_targets] at h
  obtain ⟨S, N, e, β, T, h₀, hST, hstartT, hT, hTrest⟩ := h
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let : Algebra S₀ T := (Subalgebra.inclusion h₀).toAlgebra
  let : IsScalarTower S₀ T K := Subalgebra.inclusion.isScalarTower_right h₀ K
  let κ₀T := Spec.map (CommRingCat.ofHom (algebraMap S₀ T))
  let FT : Over (Spec (.of T)) := (scalar_functor κ₀T).obj F
  obtain ⟨qT, _hqT, _hTf, hTs, _heT, ⟨k, hk⟩, htower₀⟩ := hTrest
  let : Algebra T k.val := (Subalgebra.inclusion k.property.2).toAlgebra
  let : IsScalarTower T k.val K :=
    Subalgebra.inclusion.isScalarTower_right k.property.2 K
  let κTk := Spec.map (CommRingCat.ofHom (algebraMap T k.val))
  let FTk : Over (Spec (.of k.val)) := (scalar_functor κTk).obj FT
  dsimp only [coefficient_targets] at hk
  obtain ⟨qTk, hqTk, _hnF, _hnB, _hTkf, hTks, _hek, htargets, htower₁⟩ := hk
  dsimp only [target_result] at htargets
  obtain ⟨cFM, cBM, qFM, qBM, jM, _hcFM, _hcBM, _hjM,
    _hqFM, _hqBM, _hlegsF, _hlegsB, _hlegsJ, _htriangleM, hstage⟩ := htargets
  obtain ⟨l, _hle, El, _hEl, hFLcart, hFLsnd, hclosedTargets⟩ := hstage
  let L := l.val
  have hTL : T ≤ L := k.property.2.trans l.property.2
  have h₀L : S₀ ≤ L := h₀.trans hTL
  let : Algebra T L := (Subalgebra.inclusion hTL).toAlgebra
  let : Algebra S₀ L := (Subalgebra.inclusion h₀L).toAlgebra
  let : Algebra k.val L := (Subalgebra.inclusion l.property.2).toAlgebra
  let : IsScalarTower T k.val L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower S₀ T L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower S₀ L K := Subalgebra.inclusion.isScalarTower_right h₀L K
  let κkL := Spec.map (CommRingCat.ofHom (algebraMap k.val L))
  let κ₀L := Spec.map (CommRingCat.ofHom (algebraMap S₀ L))
  let ρL := Spec.map (CommRingCat.ofHom (algebraMap L K))
  let FL : Over (Spec (.of L)) := (scalar_functor κ₀L).obj F
  let DL : Over (Spec (.of L)) := (scalar_functor κ₀L).obj D
  let Fnest : Over (Spec (.of L)) := (scalar_functor κkL).obj FTk
  let EF : Over.mk base ≅ genericScalarModel k.val FTk.hom :=
    hqTk.flip.isoOverPullback
  let qFnest : Y ⟶ Fnest.left :=
    EF.hom.left ≫ (modelScalarCone k.val FTk.hom).π.app (op l)
  change IsPullback qFnest base Fnest.hom ρL at hFLcart
  change qFnest ≫ pullback.snd κkL FTk.hom = qTk at hFLsnd
  obtain ⟨E₁, hE₁f, hE₁s⟩ := htower₁ L
  obtain ⟨E₀, hE₀f, hE₀s⟩ := htower₀ L
  let Eambient : Fnest ≅ FL := E₁ ≪≫ E₀
  have hEf : Eambient.hom.left ≫ pullback.fst κ₀L F.hom =
      pullback.fst κkL FTk.hom := by
    change (E₁.hom.left ≫ E₀.hom.left) ≫ pullback.fst κ₀L F.hom = _
    exact comp_projection E₁.hom.left E₀.hom.left _ _ _ hE₀f hE₁f
  have hEs : Eambient.hom.left ≫ pullback.snd κ₀L F.hom =
      (pullback.snd κkL FTk.hom ≫ pullback.snd κTk FT.hom) ≫
        pullback.snd κ₀T F.hom := by
    change (E₁.hom.left ≫ E₀.hom.left) ≫ pullback.snd κ₀L F.hom = _
    exact comp_projection_pair E₁.hom.left E₀.hom.left _ _ _ _ hE₀s hE₁s
  obtain ⟨qFL, hqFL, _hFLf, hFLs⟩ := scalar_flag S₀ L F (Over.mk base) qF hF
  have hqambient : qFnest ≫ Eambient.hom.left = qFL := by
    apply pullback.hom_ext
    · exact comp_projection qFnest Eambient.hom.left _ _ _ hEf
        (hFLcart.w.trans hqFL.w.symm)
    · have hNativeT : qFnest ≫
          (pullback.snd κkL FTk.hom ≫ pullback.snd κTk FT.hom) = qT :=
        successive_projections qFnest _ _ qTk qT hFLsnd hTks
      have hNativeF : qFnest ≫
          ((pullback.snd κkL FTk.hom ≫ pullback.snd κTk FT.hom) ≫
            pullback.snd κ₀T F.hom) = qF :=
        successive_projections qFnest _ _ qT qF hNativeT hTs
      exact comp_projection qFnest Eambient.hom.left _ _ _ hEs
        (hNativeF.trans hFLs.symm)
  obtain ⟨qP, hiClosed, hqP, hiTriangle, _hqPs, hPfp, hPcompact, hPqs⟩ :=
    hclosedTargets i
  let P : Over (Spec (.of L)) := stageScalarModel k.val (cBM i).pt.hom l
  let iNest : P ⟶ Fnest := chosenScalarArrow κkL (jM i) ≫ El.hom
  let iL : P ⟶ FL := iNest ≫ Eambient.hom
  change IsClosedImmersion iNest.left at hiClosed
  change IsPullback qP (j i ≫ base) P.hom ρL at hqP
  change qP ≫ iNest.left = j i ≫ qFnest at hiTriangle
  let : CompactSpace P.left := hPcompact
  let : QuasiSeparatedSpace P.left := hPqs
  let : LocallyOfFinitePresentation P.hom := hPfp
  let : IsClosedImmersion iL.left := closed_comp_iso iNest Eambient hiClosed
  have hiL : qP ≫ iL.left = j i ≫ qFL := by
    change qP ≫ (iNest.left ≫ Eambient.hom.left) = _
    exact postcompose_triangle qP iNest.left Eambient.hom.left
      (j i) qFnest qFL hiTriangle hqambient
  obtain ⟨qDL, hqDL, _hDLf, hDLs⟩ :=
    scalar_flag S₀ L D (Over.mk (j i ≫ base)) qD hD
  let dL : DL ⟶ FL := chosenScalarArrow κ₀L d
  let dN : Over.mk (j i ≫ base) ⟶ Over.mk base := Over.homMk (j i) rfl
  have hDLs' : qDL ≫ pullback.snd κ₀L D.hom = qD := hDLs
  have hFLs' : qFL ≫ pullback.snd κ₀L F.hom = qF := hFLs
  have hdL : qDL ≫ dL.left = j i ≫ qFL :=
    scalar_comparison κ₀L ρL d dN
      qD qF qDL qFL hqDL hqFL hDLs' hFLs' hd
  let rL : CoefficientStage S₀ := ⟨L, l.property.1, h₀L⟩
  have hDprops := stage_properties S₀ hS₀ D rL
  have hFprops := stage_properties S₀ hS₀ F rL
  let : CompactSpace DL.left := hDprops.2.1
  let : QuasiSeparatedSpace DL.left := hDprops.2.2
  let : LocallyOfFinitePresentation DL.hom := hDprops.1
  let : LocallyOfFinitePresentation FL.hom := hFprops.1
  obtain ⟨m, _hmstart, _Em, _hEm, _hEmInv, _hEmTriangle, hclosed⟩ :=
    exists_retained_closed_inclusion L l.property.1 DL P FL
      (j i ≫ base) qDL qP hqDL hqP dL iL (j i) qFL hdL hiL
      ⟨L, l.property.1, le_rfl⟩
  let κLm := Spec.map
    (CommRingCat.ofHom (Subalgebra.inclusion m.property.2).toRingHom)
  let : IsClosedImmersion (chosenScalarArrow κLm (chosenScalarArrow κ₀L d)).left :=
    hclosed
  have hflat : IsClosedImmersion (chosenScalarArrow (κLm ≫ κ₀L) d).left :=
    closed_scalar_tower κ₀L κLm d
  have h₀m : S₀ ≤ m.val := h₀L.trans m.property.2
  let : Algebra L m.val := (Subalgebra.inclusion m.property.2).toAlgebra
  let : Algebra S₀ m.val := (Subalgebra.inclusion h₀m).toAlgebra
  let : IsScalarTower S₀ L m.val := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hκ : κLm ≫ κ₀L =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h₀m).toRingHom) :=
    coefficient_triangle S₀ L (K := m.val)
  rw [hκ] at hflat
  refine ⟨⟨m.val, m.property.1, h₀m⟩, ?_, hflat⟩
  exact hstartT.trans (hTL.trans m.property.2)

private theorem richardson_closed_stage {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (v w : G.weylGroup)
    (S : Subalgebra ℤ K) (hS : S.FG) (D F : Over (Spec (.of S)))
    [CompactSpace D.left] [LocallyOfFinitePresentation D.hom]
    [CompactSpace F.left] [LocallyOfFinitePresentation F.hom]
    (qD : (richardsonVariety G v w).scheme ⟶ D.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (hD : IsPullback qD (richardsonVariety G v w).toSpec D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (j : D ⟶ F)
    (hj : qD ≫ j.left = (richardsonInclusion G v w).left ≫ qF)
    (start : CoefficientStage S) :
    ∃ (r : CoefficientStage S) (_ : start ≤ r),
      IsClosedImmersion (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom)) j).left := by
  classical
  let : CompactSpace (flagVariety G).scheme :=
    QuasiCompact.compactSpace_of_compactSpace (flagVariety G).toSpec
  let V := (flagVariety G).scheme.affineCover.finiteSubcover
  let U : V.I₀ → (flagVariety G).scheme.Opens := fun t => (V.f t).opensRange
  have hV (t : V.I₀) : IsAffine (V.X t) := by
    change IsAffine ((flagVariety G).scheme.affineCover.X _)
    infer_instance
  have hU (t : V.I₀) : IsAffineOpen (U t) := by
    let : IsAffine (V.X t) := hV t
    exact isAffineOpen_opensRange (V.f t)
  have hcover : (⨆ t, U t) = ⊤ := V.iSup_opensRange
  let Z : PUnit.{u+1} → TopologicalSpace.Closeds (flagVariety G).scheme :=
    fun _ => richardsonSupport G v w
  let X : PUnit.{u+1} → Scheme.{u} := fun _ => (richardsonVariety G v w).scheme
  let jN : ∀ i, X i ⟶ (flagVariety G).scheme :=
    fun _ => (richardsonInclusion G v w).left
  let : IsAffineHom (pullback.diagonal (terminal.from (flagVariety G).scheme)) :=
    variety_diagonal (flagVariety G)
  let hDiag : ∀ i : PUnit.{u+1},
      IsAffineHom (pullback.diagonal (terminal.from (X i))) :=
    fun _ => variety_diagonal (richardsonVariety G v w)
  let hClosed : ∀ i : PUnit.{u+1}, IsClosedImmersion (jN i) :=
    fun _ => inferInstanceAs (IsClosedImmersion (richardsonInclusion G v w).left)
  have htargets : @common_targets _ _ _ _ _ _ X hDiag jN hClosed
      (flagVariety G).toSpec U hU S F qF start :=
    exists_closed_flag_common G Z U hU hcover S hS F qF hF start
  have hD' : IsPullback qD (jN PUnit.unit ≫ (flagVariety G).toSpec) D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) := by
    have hjbase : jN PUnit.unit ≫ (flagVariety G).toSpec =
        (richardsonVariety G v w).toSpec := (richardsonInclusion G v w).w
    rw [hjbase]
    exact hD
  exact @closed_from_common_targets _ _ _ _ _ _ X hDiag jN hClosed
    (flagVariety G).toSpec U hU S hS D F _ _ _ _
    PUnit.unit qD qF hD' hF j hj start htargets

end SchubertGeometry
