import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BaseChange
import OrbitComplexity.SchubertGeometry.BSDH.FiniteCover

/-! # Finite integral projective-line charts for BSDH append maps -/

noncomputable section

universe u v w

namespace SchubertGeometry

section Part1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory

section Affine

variable (K : Type u) [CommRing K] (U : Over (Spec (.of K))) [IsAffine U.left]

private noncomputable def affineCoordinatesIso :
    U ≅ (algSpec (.of K)).obj ((algΓ (.of K)).obj U) := by
  have : IsIso ((algΓAlgSpecAdjunction (.of K)).unit.app U) :=
    FrobeniusSplitting.coordinates_unit_isIso (.of K) U
  exact asIso ((algΓAlgSpecAdjunction (.of K)).unit.app U)

private noncomputable def affineLineProductIso :
    GroupActions.projectiveScheme ((algΓ (.of K)).obj U).unop (ULift.{u} (Fin 2)) ≅
      (U ⊗ Over.mk (GroupActions.projectiveToSpec K (ULift.{u} (Fin 2)))).left := by
  let A := ((algΓ (.of K)).obj U).unop
  let V := (algSpec (.of K)).obj ((algΓ (.of K)).obj U)
  let Y := Over.mk (GroupActions.projectiveToSpec K (ULift.{u} (Fin 2)))
  let e : GroupActions.projectiveScheme A (ULift.{u} (Fin 2)) ≅ (V ⊗ Y).left :=
    GroupActions.projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K A)
  exact e ≪≫ (Over.forget (Spec (.of K))).mapIso
    (tensorIso (affineCoordinatesIso K U).symm (Iso.refl Y))

private theorem affineLineProductIso_fst :
    (affineLineProductIso K U).hom ≫
      (fst U (Over.mk (GroupActions.projectiveToSpec K (ULift.{u} (Fin 2))))).left =
        GroupActions.projectiveToSpec ((algΓ (.of K)).obj U).unop (ULift.{u} (Fin 2)) ≫
          (affineCoordinatesIso K U).inv.left := by
  let A := ((algΓ (.of K)).obj U).unop
  let V := (algSpec (.of K)).obj ((algΓ (.of K)).obj U)
  let Y := Over.mk (GroupActions.projectiveToSpec K (ULift.{u} (Fin 2)))
  let e : GroupActions.projectiveScheme A (ULift.{u} (Fin 2)) ≅ (V ⊗ Y).left :=
    GroupActions.projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K A)
  let d := tensorIso (affineCoordinatesIso K U).symm (Iso.refl Y)
  have ht : (tensorIso (affineCoordinatesIso K U).symm (Iso.refl Y)).hom ≫ fst U Y =
      fst V Y ≫ (affineCoordinatesIso K U).inv := by
    simp only [tensorIso_hom, Iso.symm_hom, Iso.refl_hom, tensorHom_fst]
    rfl
  have hs : d.hom.left ≫ (fst U Y).left =
      (fst V Y).left ≫ (affineCoordinatesIso K U).inv.left :=
    congrArg (fun f => f.left) ht
  have he : e.hom ≫ (fst V Y).left =
      GroupActions.projectiveToSpec A (ULift.{u} (Fin 2)) :=
    GroupActions.projectiveBaseChange_fst (ULift.{u} (Fin 2)) (algebraMap K A)
  change (e.hom ≫ d.hom.left) ≫ (fst U Y).left = _
  calc
    _ = e.hom ≫ (d.hom.left ≫ (fst U Y).left) := Category.assoc _ _ _
    _ = e.hom ≫ ((fst V Y).left ≫ (affineCoordinatesIso K U).inv.left) :=
      congrArg (fun f => e.hom ≫ f) hs
    _ = (e.hom ≫ (fst V Y).left) ≫ (affineCoordinatesIso K U).inv.left :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ (affineCoordinatesIso K U).inv.left) he

end Affine

section BSDH

attribute [local instance] ULift.algebra'

/-- A finite BSDH append cover is given by integral projective-line models over affine bases. -/
theorem bsdh_finite_integer_cover {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) :
    ∃ 𝒰 : (bsdhScheme G word).OpenCover.{u}, Finite 𝒰.I₀ ∧
      (∀ j, IsAffine (𝒰.X j)) ∧
      let 𝒲 := 𝒰.pullback₁ (bsdhAppendFst G word i)
      Finite 𝒲.I₀ ∧ ∀ j : 𝒰.I₀,
        ∃ (A : CommAlgCat.{u} K)
          (a : (algSpec (.of K)).obj (.op A) ≅ Over.mk (𝒰.f j ≫ bsdhToSpec G word))
          (e : (integralLineIntegerCocone A).pt.left ≅ 𝒲.X j),
          Nonempty (IsColimit (integralLineIntegerCocone A)) ∧
          IsProper (integralLineIntegerCocone A).pt.hom ∧
          Smooth (integralLineIntegerCocone A).pt.hom ∧
          GeometricallyConnected (integralLineIntegerCocone A).pt.hom ∧
          e.hom ≫ 𝒰.pullbackHom (bsdhAppendFst G word i) j =
            GroupActions.projectiveToSpec A (ULift.{u} (Fin 2)) ≫ a.hom.left := by
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  obtain ⟨𝒰, hfinite, haffine, hW, hcharts⟩ := bsdh_finite_bundle_cover G word i
  let 𝒲 := 𝒰.pullback₁ (bsdhAppendFst G word i)
  refine ⟨𝒰, hfinite, haffine, hW, fun j ↦ ?_⟩
  let U := Over.mk (𝒰.f j ≫ bsdhToSpec G word)
  let : IsAffine U.left := haffine j
  let A := ((algΓ (.of K)).obj U).unop
  let a := (affineCoordinatesIso K U).symm
  let P := Over.mk (GroupActions.projectiveToSpec K (ULift.{u} (Fin 2)))
  let t : U ⊗ P ≅ U ⊗ Y.toOver :=
    tensorIso (Iso.refl U) (simpleSchubertIso G i).symm
  let d := (Over.forget (Spec (.of K))).mapIso t
  let c := affineLineProductIso K U ≪≫ d
  obtain ⟨b, hb, _, _⟩ := hcharts j
  let e := c ≪≫ b
  have ht : t.hom ≫ fst U Y.toOver = fst U P := by
    change (𝟙 U ⊗ₘ (simpleSchubertIso G i).inv) ≫ fst U Y.toOver = fst U P
    exact (tensorHom_fst _ _).trans (Category.comp_id _)
  have hd : d.hom ≫ (fst U Y.toOver).left = (fst U P).left :=
    congrArg (fun f => f.left) ht
  have hc : c.hom ≫ (fst U Y.toOver).left =
      GroupActions.projectiveToSpec A (ULift.{u} (Fin 2)) ≫ a.hom.left := by
    change ((affineLineProductIso K U).hom ≫ d.hom) ≫ _ = _
    calc
      _ = (affineLineProductIso K U).hom ≫ (d.hom ≫ (fst U Y.toOver).left) :=
        Category.assoc _ _ _
      _ = (affineLineProductIso K U).hom ≫ (fst U P).left :=
        congrArg (fun f => (affineLineProductIso K U).hom ≫ f) hd
      _ = _ := affineLineProductIso_fst K U
  have hgeom := (integralLineInteger_properties A).2
  refine ⟨A, a, e, ⟨integralLineIntegerColimit A⟩,
    hgeom.1, hgeom.2.1, hgeom.2.2, ?_⟩
  change (c.hom ≫ b.hom) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => c.hom ≫ f) hb).trans hc)

end BSDH

end Part1

end SchubertGeometry
