import OrbitComplexity.FrobeniusSplitting.Normality.Limits.CoefficientLimit
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Finite-stage morphisms on coefficient pullbacks -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FrobeniusSplitting

universe u

/-- The original coefficient stages as schemes over the prescribed base. -/
def coefficientOverStages {K : Type u} [CommRing K] (S : Subalgebra ℤ K) :
    (CoefficientStage S)ᵒᵖ ⥤ Over (Spec (.of S)) :=
  (coefficientSchemes S).toOver (Spec (.of S))
    (fun i => Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion i.unop.property.2).toRingHom))
    (by
      intro i j f
      exact (Spec.map_comp
        (CommRingCat.ofHom (Subalgebra.inclusion j.unop.property.2).toRingHom)
        ((coefficientRings S).map f.unop)).symm)

/-- The cone retains the given Spec K to Spec S morphism. -/
def coefficientOverCone {K : Type u} [CommRing K] (S : Subalgebra ℤ K) :
    Cone (coefficientOverStages S) where
  pt := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap S K)))
  π :=
    { app := fun i => Over.homMk ((coefficientSpecCone S).π.app i) (by
        exact (Spec.map_comp
          (CommRingCat.ofHom (Subalgebra.inclusion i.unop.property.2).toRingHom)
          (CommRingCat.ofHom (algebraMap i.unop.val K))).symm)
      naturality := fun i j f => by
        apply Over.OverMorphism.ext
        exact (Category.id_comp _).trans ((coefficientSpecCone S).w f).symm }

/-- The coefficient cone is limiting over the same Spec S. -/
def coefficientOverLimit {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG) : IsLimit (coefficientOverCone S) := by
  let h := coefficientSpecLimit S hS
  let i : (CoefficientStage S)ᵒᵖ := op ⟨S, hS, le_rfl⟩
  refine
    { lift := fun s => Over.homMk (h.lift ((Over.forget _).mapCone s)) ?_
      fac := fun s j => ?_
      uniq := fun s m hm => ?_ }
  · calc
      h.lift ((Over.forget _).mapCone s) ≫ (coefficientOverCone S).pt.hom =
          h.lift ((Over.forget _).mapCone s) ≫
            (((coefficientOverCone S).π.app i).left ≫
              ((coefficientOverStages S).obj i).hom) := by
        exact congrArg (fun q => h.lift ((Over.forget _).mapCone s) ≫ q)
          ((coefficientOverCone S).π.app i).w.symm
      _ = (s.π.app i).left ≫ ((coefficientOverStages S).obj i).hom := by
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun q => q ≫ ((coefficientOverStages S).obj i).hom)
            (h.fac ((Over.forget _).mapCone s) i))
      _ = s.pt.hom := (s.π.app i).w
  · apply Over.OverMorphism.ext
    exact h.fac ((Over.forget _).mapCone s) j
  · apply Over.OverMorphism.ext
    apply h.uniq ((Over.forget _).mapCone s) m.left
    intro j
    exact congrArg Over.Hom.left (hm j)

/-- Every stage is the pullback of the specified model, with Spec R first. -/
def modelScalarStages {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) :
    (CoefficientStage S)ᵒᵖ ⥤ Scheme.{u} :=
  coefficientOverStages S ⋙ Over.pullback a ⋙ Over.forget X

/-- The apex is the K-pullback of the specified model. -/
def modelScalarCone {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) : Cone (modelScalarStages S a) :=
  (Over.forget X).mapCone ((Over.pullback a).mapCone (coefficientOverCone S))

/-- coefficient pullbacks of a fixed scheme recover its K-fibre. -/
def modelScalarLimit {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) (hS : S.FG)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) : IsLimit (modelScalarCone S a) := by
  letI : Nonempty (CoefficientStage S) := ⟨⟨S, hS, le_rfl⟩⟩
  exact isLimitOfPreserves (Over.forget X)
    (isLimitOfPreserves (Over.pullback a) (coefficientOverLimit S hS))

/-- Transition morphisms between scalar models are affine. -/
instance {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) {i j : (CoefficientStage S)ᵒᵖ}
    (f : i ⟶ j) : IsAffineHom ((modelScalarStages S a).map f) := by
  exact MorphismProperty.overPullbackMap (P := @IsAffineHom) a
    ((coefficientOverStages S).map f) (by
      change IsAffineHom (Spec.map _)
      infer_instance)

private theorem stageProjection_affine {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    (i : (CoefficientStage S)ᵒᵖ) :
    IsAffineHom (pullback.snd ((coefficientOverStages S).obj i).hom a) := by
  let P : MorphismProperty Scheme.{u} := @IsAffineHom
  let : P.IsStableUnderBaseChange := isAffineHom_isStableUnderBaseChange
  have h : P ((coefficientOverStages S).obj i).hom := by
    change IsAffineHom (Spec.map _)
    infer_instance
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P)
    (IsPullback.of_hasPullback ((coefficientOverStages S).obj i).hom a) h

/-- Scalar models of a compact scheme are compact. -/
instance {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} [CompactSpace X] (a : X ⟶ Spec (.of S))
    (i : (CoefficientStage S)ᵒᵖ) : CompactSpace ((modelScalarStages S a).obj i) := by
  change CompactSpace (pullback ((coefficientOverStages S).obj i).hom a : Scheme.{u})
  let : IsAffineHom (pullback.snd ((coefficientOverStages S).obj i).hom a) :=
    stageProjection_affine S a i
  exact QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd ((coefficientOverStages S).obj i).hom a)

/-- Scalar models of a quasi-separated scheme are quasi-separated. -/
instance {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} [QuasiSeparatedSpace X] (a : X ⟶ Spec (.of S))
    (i : (CoefficientStage S)ᵒᵖ) : QuasiSeparatedSpace ((modelScalarStages S a).obj i) := by
  change QuasiSeparatedSpace
    (pullback ((coefficientOverStages S).obj i).hom a : Scheme.{u})
  let : IsAffineHom (pullback.snd ((coefficientOverStages S).obj i).hom a) :=
    stageProjection_affine S a i
  exact quasiSeparatedSpace_of_quasiSeparated
    (pullback.snd ((coefficientOverStages S).obj i).hom a)

/-- The stage base maps come from the original model projection. -/
def modelScalarBase {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of S)) :
    modelScalarStages S a ⟶ (Functor.const _).obj (Spec (.of S)) where
  app i := ((Over.pullback a).obj ((coefficientOverStages S).obj i)).hom ≫ a
  naturality i j f := by
    change (((Over.pullback a).map ((coefficientOverStages S).map f)).left ≫
      (((Over.pullback a).obj ((coefficientOverStages S).obj j)).hom ≫ a)) =
        ((((Over.pullback a).obj ((coefficientOverStages S).obj i)).hom ≫ a) ≫ 𝟙 _)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ a)
        (((Over.pullback a).map ((coefficientOverStages S).map f)).w)).trans
          (Category.comp_id _).symm)

/-- A morphism descends to a coefficient pullback of the
same source model. Its structure triangle and its original map are retained. -/
theorem exists_scalar_morphism
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S))
    [LocallyOfFinitePresentation b]
    (g : (modelScalarCone S a).pt ⟶ Y)
    (hg : g ≫ b = pullback.snd _ a ≫ a) :
    ∃ (i : CoefficientStage S) (f : (modelScalarStages S a).obj (op i) ⟶ Y),
      (modelScalarCone S a).π.app (op i) ≫ f = g ∧
      f ≫ b = (modelScalarBase S a).app (op i) := by
  let : Nonempty (CoefficientStage S) := ⟨⟨S, hS, le_rfl⟩⟩
  have hbase : (modelScalarCone S a).π ≫ modelScalarBase S a =
      (Functor.const _).map (g ≫ b) := by
    ext i
    change (((Over.pullback a).map ((coefficientOverCone S).π.app i)).left ≫
      (((Over.pullback a).obj ((coefficientOverStages S).obj i)).hom ≫ a)) = g ≫ b
    rw [← Category.assoc, Over.w]
    exact hg.symm
  obtain ⟨i, f, hnative, htriangle⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (modelScalarStages S a) (modelScalarBase S a) b
      (modelScalarCone S a) (modelScalarLimit S hS a) g hbase
  exact ⟨i.unop, f, hnative, htriangle⟩


end FrobeniusSplitting
