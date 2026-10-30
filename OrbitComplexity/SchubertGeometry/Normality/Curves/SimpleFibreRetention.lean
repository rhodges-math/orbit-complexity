import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelIsoDescent
import OrbitComplexity.SchubertGeometry.Parabolics.CurveFibre
import OrbitComplexity.SchubertGeometry.ProjectiveLine.IsoGluing
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange

/-! # The simple P1 fibre on the specified flag and partial-flag models -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups
open FrobeniusSplitting

namespace SchubertGeometry

universe u

/-- The simple curve identifies the generic fibre of the model
fibre with the generic fibre of the canonical projective-line model. -/
def simpleFibreModelIso
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (G : ReductiveGroupData K)
    (w : G.weylGroup) (i : G.rootBase.support)
    (F Q : Over (Spec (.of S))) (π : F ⟶ Q)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qQ : (partialFlagVariety G {i}).scheme ⟶ Q.left)
    (hπ : IsPullback (partialFlagMorphism G {i}).left qF qQ π.left)
    (b : Over.mk (𝟙 (Spec (.of S))) ⟶ Q)
    (hb : ((weylFlagPoint G w).val ≫ (partialFlagMorphism G {i}).left) ≫ qQ =
      Spec.map (CommRingCat.ofHom (algebraMap S K)) ≫ b.left) :
    genericScalarModel S (projectiveToSpec S (ULift.{u} (Fin 2))) ≅
      genericScalarModel S (pullback.snd π.left b.left) := by
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let X := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let d := (simpleSchubertCurve G w i).left
  have hout : IsPullback (d ≫ qF) X.toSpec π.left (κ ≫ b.left) := by
    rw [← hb]
    exact (simpleSchubertCurve_isPullback G w i).paste_horiz hπ.flip
  let qD : X.scheme ⟶ pullback π.left b.left :=
    pullback.lift (d ≫ qF) (X.toSpec ≫ κ) (by
      rw [Category.assoc]
      exact hout.w)
  have houter : IsPullback (qD ≫ pullback.fst π.left b.left)
      X.toSpec π.left (κ ≫ b.left) := by
    change IsPullback (pullback.lift _ _ _ ≫ pullback.fst _ _) _ _ _
    rw [pullback.lift_fst]
    exact hout
  have hD : IsPullback qD X.toSpec (pullback.snd π.left b.left) κ :=
    houter.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback π.left b.left)
  let eD : X.toOver ≅ genericScalarModel S (pullback.snd π.left b.left) :=
    Over.isoMk hD.flip.isoPullback hD.flip.isoPullback_hom_fst
  let eP : (projectiveVariety K (ULift.{u} (Fin 2))).toOver ≅
      genericScalarModel S (projectiveToSpec S (ULift.{u} (Fin 2))) :=
    Over.isoMk (projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap S K))
      (projectiveBaseChange_fst _ _)
  exact eP.symm ≪≫ (simpleSchubertIso G i).symm ≪≫ eD

/-- The simple-incidence fibre becomes a projective line on one enlarged
coefficient ring. Its comparison is constructed from the original chosen
projection and Weyl-point section, with no projective-fibre conclusion assumed. -/
theorem exists_simple_fibre_model
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (w : G.weylGroup) (i : G.rootBase.support)
    (F Q : Over (Spec (.of S))) (π : F ⟶ Q)
    [LocallyOfFinitePresentation π.left] [QuasiCompact π.left] [IsSeparated π.left]
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qQ : (partialFlagVariety G {i}).scheme ⟶ Q.left)
    (hπ : IsPullback (partialFlagMorphism G {i}).left qF qQ π.left)
    (b : Over.mk (𝟙 (Spec (.of S))) ⟶ Q)
    (hb : ((weylFlagPoint G w).val ≫ (partialFlagMorphism G {i}).left) ≫ qQ =
      Spec.map (CommRingCat.ofHom (algebraMap S K)) ≫ b.left) :
    let E := SchubertGeometry.simpleFibreModelIso S G w i F Q π qF qQ hπ b hb
    ∃ (r : CoefficientStage S)
      (E₀ : stageScalarModel S (projectiveToSpec S (ULift.{u} (Fin 2))) r ≅
        stageScalarModel S (pullback.snd π.left b.left) r),
      ((modelScalarCone S (projectiveToSpec S (ULift.{u} (Fin 2)))).π.app
          (Opposite.op r) ≫ E₀.hom.left =
        E.hom.left ≫ (modelScalarCone S (pullback.snd π.left b.left)).π.app
          (Opposite.op r)) ∧
      ((modelScalarCone S (pullback.snd π.left b.left)).π.app (Opposite.op r) ≫
          E₀.inv.left = E.inv.left ≫
        (modelScalarCone S (projectiveToSpec S (ULift.{u} (Fin 2)))).π.app
          (Opposite.op r)) := by
  let D : Scheme.{u} := pullback π.left b.left
  let aD : D ⟶ Spec (.of S) := pullback.snd π.left b.left
  let : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace aD
  let : QuasiSeparatedSpace D := quasiSeparatedSpace_of_quasiSeparated aD
  let : CompactSpace (projectiveScheme S (ULift.{u} (Fin 2))) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveToSpec S (ULift.{u} (Fin 2)))
  let : QuasiSeparatedSpace (projectiveScheme S (ULift.{u} (Fin 2))) :=
    quasiSeparatedSpace_of_quasiSeparated (projectiveToSpec S (ULift.{u} (Fin 2)))
  exact exists_model_iso S hS (projectiveToSpec S (ULift.{u} (Fin 2))) aD
    (SchubertGeometry.simpleFibreModelIso S G w i F Q π qF qQ hπ b hb)


end SchubertGeometry
