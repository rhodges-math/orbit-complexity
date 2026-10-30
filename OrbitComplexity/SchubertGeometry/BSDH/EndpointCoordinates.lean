import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BaseChange
import Mathlib.AlgebraicGeometry.Cover.Directed
import OrbitComplexity.FrobeniusSplitting.Normality.CoordinateComparisons
import OrbitComplexity.SchubertGeometry.BSDH.EndpointCharts

/-! # Canonical integral coordinate covers of endpoint charts -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory

noncomputable section
universe u v w
namespace SchubertGeometry

@[implicit_reducible]
private noncomputable def specifiedCoconeCover {J : Type v} [Category.{w} J]
    [Quiver.IsThin J] [Small.{u} J] (F : J ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
    [(F ⋙ Scheme.forget).IsLocallyDirected] (c : Cocone F) (hc : IsColimit c) :
    c.pt.OpenCover.{v} := by
  let e := (colimit.isColimit F).coconePointUniqueUpToIso hc
  have hleg (i : J) : colimit.ι F i ≫ e.hom = c.ι.app i :=
    (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hc i
  refine
    { I₀ := J
      X := F.obj
      f := c.ι.app
      mem₀ := ?_ }
  rw [Scheme.presieve₀_mem_precoverage_iff]
  refine ⟨fun y ↦ ?_, fun i ↦ ?_⟩
  · obtain ⟨i, x, hx⟩ := (Scheme.IsLocallyDirected.openCover F).exists_eq (e.inv y)
    change J at i
    change F.obj i at x
    change (colimit.ι F i) x = e.inv y at hx
    refine ⟨i, x, ?_⟩
    have h := congrArg (fun f : F.obj i ⟶ c.pt ↦ f x) (hleg i)
    change e.hom ((colimit.ι F i) x) = (c.ι.app i) x at h
    exact h.symm.trans ((congrArg e.hom hx).trans
      (congrArg (fun f : c.pt ⟶ c.pt ↦ f y) e.inv_hom_id))
  · change J at i
    change IsOpenImmersion (c.ι.app i)
    rw [← hleg i]
    infer_instance

@[implicit_reducible]
private noncomputable def lineCoordinateCover (R : Type u) [CommRing R] :
    (GroupActions.projectiveScheme R (ULift.{u} (Fin 2))).OpenCover.{u} := by
  have {s t : ProjectiveLineIndex.{u}ᵒᵖ} (f : s ⟶ t) :
      IsOpenImmersion
        (((projectiveLineDiagram R).op ⋙ algSpec (.of R) ⋙
          Over.forget (Spec (.of R))).map f) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
      ((projectiveLineDiagram R).map f.unop).hom.toRingHom)))
  have : (((projectiveLineDiagram R).op ⋙ algSpec (.of R) ⋙
      Over.forget (Spec (.of R))) ⋙ Scheme.forget).IsLocallyDirected :=
    projectiveLineDiagram_directed R
  exact specifiedCoconeCover
    ((projectiveLineDiagram R).op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)))
    ((Over.forget (Spec (.of R))).mapCocone (projectiveLineCocone R))
    (isColimitOfPreserves (Over.forget (Spec (.of R))) (projectiveLineCoconeIsColimit R))

end SchubertGeometry

namespace SchubertGeometry

@[implicit_reducible]
private noncomputable def integerLineAffineCover (R : Type u) [CommRing R]
    [Algebra (ULift.{u} ℤ) R] :
    ((integralLineIntegerCocone R).pt.left).OpenCover.{u} := by
  let C := lineCoordinateCover R
  let e : (FrobeniusSplitting.integerFibreDiagram R
      (projectiveLineDiagram (ULift.{u} ℤ))).op ⋙ algSpec (.of R) ≅
        (projectiveLineDiagram R).op ⋙ algSpec (.of R) :=
    Functor.isoWhiskerRight (NatIso.op (integralLineIntegerIso R).symm) (algSpec (.of R))
  have hleg (s : ProjectiveLineIndex.{u}ᵒᵖ) :
      ((integralLineIntegerCocone R).ι.app s).left =
        (e.hom.app s).left ≫ C.f s := rfl
  refine
    { I₀ := ProjectiveLineIndex.{u}ᵒᵖ
      X := fun s ↦ Spec (.of ((FrobeniusSplitting.integerFibreDiagram R
        (projectiveLineDiagram (ULift.{u} ℤ))).obj s.unop))
      f := fun s ↦ ((integralLineIntegerCocone R).ι.app s).left
      mem₀ := ?_ }
  rw [Scheme.presieve₀_mem_precoverage_iff]
  refine ⟨fun y ↦ ?_, fun s ↦ ?_⟩
  · obtain ⟨s, x, hx⟩ := C.exists_eq y
    change ProjectiveLineIndex.{u}ᵒᵖ at s
    let d := (Over.forget (Spec (.of R))).mapIso (e.app s)
    refine ⟨s, d.inv x, ?_⟩
    have h := congrArg (fun f : Spec (.of
        ((FrobeniusSplitting.integerFibreDiagram R
          (projectiveLineDiagram (ULift.{u} ℤ))).obj s.unop)) ⟶
        GroupActions.projectiveScheme R (ULift.{u} (Fin 2)) ↦ f (d.inv x)) (hleg s)
    change ((integralLineIntegerCocone R).ι.app s).left (d.inv x) =
      C.f s (d.hom (d.inv x)) at h
    have hd := congrArg (fun f ↦ f x) d.inv_hom_id
    exact h.trans ((congrArg (C.f s) hd).trans hx)
  · change ProjectiveLineIndex.{u}ᵒᵖ at s
    change IsOpenImmersion ((integralLineIntegerCocone R).ι.app s).left
    rw [hleg]
    have he : IsOpenImmersion (e.hom.app s).left :=
      inferInstanceAs (IsOpenImmersion
        (((Over.forget (Spec (.of R))).mapIso (e.app s)).hom))
    exact @IsOpenImmersion.comp _ _ _ _ _ he (C.map_prop s)

end SchubertGeometry



namespace SchubertGeometry

attribute [local instance] ULift.algebra'

@[implicit_reducible]
private noncomputable def familyBundleCover {X : Scheme.{u}}
    (𝒲 : X.OpenCover.{u}) (Y : 𝒲.I₀ → Scheme.{u})
    (C : ∀ j, (Y j).OpenCover.{u}) (b : ∀ j, Y j ≅ 𝒲.X j) : X.OpenCover.{u} := by
  refine
    { I₀ := Σ j : 𝒲.I₀, (C j).I₀
      X := fun k ↦ (C k.1).X k.2
      f := fun k ↦ (C k.1).f k.2 ≫ (b k.1).hom ≫ 𝒲.f k.1
      mem₀ := ?_ }
  rw [Scheme.presieve₀_mem_precoverage_iff]
  refine ⟨fun y ↦ ?_, fun k ↦ ?_⟩
  · obtain ⟨j, x, hx⟩ := 𝒲.exists_eq y
    obtain ⟨s, z, hz⟩ := (C j).exists_eq ((b j).inv x)
    refine ⟨⟨j, s⟩, z, ?_⟩
    change 𝒲.f j ((b j).hom ((C j).f s z)) = y
    have hd := congrArg (fun f : 𝒲.X j ⟶ 𝒲.X j ↦ f x) (b j).inv_hom_id
    exact (congrArg (fun q ↦ 𝒲.f j ((b j).hom q)) hz).trans
      ((congrArg (𝒲.f j) hd).trans hx)
  · change (Σ j : 𝒲.I₀, (C j).I₀) at k
    rcases k with ⟨j, s⟩
    have hb : IsOpenImmersion (b j).hom := inferInstance
    have hw : IsOpenImmersion ((b j).hom ≫ 𝒲.f j) :=
      @IsOpenImmersion.comp _ _ _ _ _ hb (𝒲.map_prop j)
    exact @IsOpenImmersion.comp _ _ _ _ _ ((C j).map_prop s) hw

end SchubertGeometry

namespace SchubertGeometry

attribute [local instance] ULift.algebra'

/-- Finite projective-line product covers refine by the three canonical coordinate spectra. -/
private theorem exists_integerBundleCover (K : Type u) [CommRing K]
    {X : Scheme.{u}} (𝒲 : X.OpenCover.{u}) [Finite 𝒲.I₀]
    (A : 𝒲.I₀ → CommAlgCat.{u} K)
    (b : ∀ j, (integralLineIntegerCocone (A j)).pt.left ≅ 𝒲.X j) :
    ∃ 𝒱 : X.OpenCover.{u}, Finite 𝒱.I₀ ∧ (∀ k, IsAffine (𝒱.X k)) ∧
      ∃ (label : 𝒱.I₀ → 𝒲.I₀) (node : 𝒱.I₀ → ProjectiveLineIndex.{u})
        (e : ∀ k, Spec (.of ((FrobeniusSplitting.integerFibreDiagram (A (label k))
          (projectiveLineDiagram (ULift.{u} ℤ))).obj (node k))) ≅ 𝒱.X k),
        Function.Bijective (fun k : 𝒱.I₀ ↦
          (⟨label k, node k⟩ : Σ _ : 𝒲.I₀, ProjectiveLineIndex.{u})) ∧
        ∀ k, (e k).hom ≫ 𝒱.f k =
          ((integralLineIntegerCocone (A (label k))).ι.app (.op (node k))).left ≫
            (b (label k)).hom ≫ 𝒲.f (label k) := by
  classical
  let Y (j : 𝒲.I₀) : Scheme.{u} := (integralLineIntegerCocone (A j)).pt.left
  let C (j : 𝒲.I₀) : (Y j).OpenCover.{u} := integerLineAffineCover (A j)
  let 𝒱 := familyBundleCover 𝒲 Y C b
  have hV : Finite 𝒱.I₀ := by
    change Finite (Σ _ : 𝒲.I₀, ProjectiveLineIndex.{u}ᵒᵖ)
    infer_instance
  let label : 𝒱.I₀ → 𝒲.I₀ := fun k ↦ k.1
  let node : 𝒱.I₀ → ProjectiveLineIndex.{u} := fun k ↦ k.2.unop
  let e : ∀ k, Spec (.of ((FrobeniusSplitting.integerFibreDiagram (A (label k))
      (projectiveLineDiagram (ULift.{u} ℤ))).obj (node k))) ≅ 𝒱.X k :=
    fun k ↦ Iso.refl _
  refine ⟨𝒱, hV, ?_, ?_⟩
  · intro k
    change IsAffine (Spec (.of ((FrobeniusSplitting.integerFibreDiagram (A k.1)
      (projectiveLineDiagram (ULift.{u} ℤ))).obj k.2.unop)))
    infer_instance
  · refine ⟨label, node, e, ?_, ?_⟩
    · constructor
      · intro k l h
        change (⟨k.1, k.2.unop⟩ : Σ _ : 𝒲.I₀, ProjectiveLineIndex.{u}) =
          ⟨l.1, l.2.unop⟩ at h
        exact congrArg (fun t : Σ _ : 𝒲.I₀, ProjectiveLineIndex.{u} ↦
          (⟨t.1, Opposite.op t.2⟩ : Σ _ : 𝒲.I₀, ProjectiveLineIndex.{u}ᵒᵖ)) h
      · rintro ⟨j, s⟩
        exact ⟨⟨j, .op s⟩, rfl⟩
    · intro k
      change (𝟙 _ ≫ (((integralLineIntegerCocone (A k.1)).ι.app k.2).left ≫
        (b k.1).hom ≫ 𝒲.f k.1)) =
          ((integralLineIntegerCocone (A k.1)).ι.app k.2).left ≫ (b k.1).hom ≫ 𝒲.f k.1
      exact Category.id_comp _


end SchubertGeometry

namespace SchubertGeometry
attribute [local instance] ULift.algebra'

/-- The product-fibre coordinates determined by a specified affine presentation. -/
def projectiveFibreIso (K : Type u) [CommRing K] (A : CommAlgCat.{u} K)
    (U Y : Over (Spec (.of K)))
    (a : (algSpec (.of K)).obj (.op A) ≅ U)
    (y : Y ≅ Over.mk (GroupActions.projectiveToSpec K (ULift.{u} (Fin 2)))) :
    GroupActions.projectiveScheme A (ULift.{u} (Fin 2)) ≅ (U ⊗ Y).left :=
  GroupActions.projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K A) ≪≫
    (Over.forget (Spec (.of K))).mapIso (tensorIso a y.symm)

private theorem projectiveFibreIso_fst (K : Type u) [CommRing K] (A : CommAlgCat.{u} K)
    (U Y : Over (Spec (.of K))) (a : (algSpec (.of K)).obj (.op A) ≅ U)
    (y : Y ≅ Over.mk (GroupActions.projectiveToSpec K (ULift.{u} (Fin 2)))) :
    (projectiveFibreIso K A U Y a y).hom ≫ (fst U Y).left =
      GroupActions.projectiveToSpec A (ULift.{u} (Fin 2)) ≫ a.hom.left := by
  let V := (algSpec (.of K)).obj (.op A)
  let P := Over.mk (GroupActions.projectiveToSpec K (ULift.{u} (Fin 2)))
  let e := GroupActions.projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap K A)
  let d := tensorIso a y.symm
  have hd : d.hom ≫ fst U Y = fst V P ≫ a.hom := by
    simp only [d, tensorIso_hom, Iso.symm_hom, tensorHom_fst]
    rfl
  have he : e.hom ≫ (fst V P).left =
      GroupActions.projectiveToSpec A (ULift.{u} (Fin 2)) :=
    GroupActions.projectiveBaseChange_fst (ULift.{u} (Fin 2)) (algebraMap K A)
  change (e.hom ≫ d.hom.left) ≫ (fst U Y).left = _
  calc
    _ = e.hom ≫ (d.hom.left ≫ (fst U Y).left) := Category.assoc _ _ _
    _ = e.hom ≫ ((fst V P).left ≫ a.hom.left) :=
      congrArg (fun f ↦ e.hom ≫ f.left) hd
    _ = (e.hom ≫ (fst V P).left) ≫ a.hom.left := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f ↦ f ≫ a.hom.left) he

private theorem productCoordinates (K : Type u) [CommRing K] (A : CommAlgCat.{u} K)
    (U Y : Over (Spec (.of K))) (a : (algSpec (.of K)).obj (.op A) ≅ U)
    (y : Y ≅ Over.mk (GroupActions.projectiveToSpec K (ULift.{u} (Fin 2))))
    {X T Q : Scheme.{u}} (f : T ⟶ X) (b : U.left ⟶ X)
    (c : (U ⊗ Y).left ⟶ T) (hcart : IsPullback (fst U Y).left c b f)
    (r : T ⟶ Q) (t : (U ⊗ Y).left ⟶ Q) (hend : c ≫ r = t) :
    let p := projectiveFibreIso K A U Y a y
    ∃ e : GroupActions.projectiveScheme A (ULift.{u} (Fin 2)) ≅ pullback f b,
      e.hom ≫ pullback.fst f b = p.hom ≫ c ∧
      e.hom ≫ pullback.snd f b =
        GroupActions.projectiveToSpec A (ULift.{u} (Fin 2)) ≫ a.hom.left ∧
      (e.hom ≫ pullback.fst f b) ≫ r = p.hom ≫ t := by
  let p := projectiveFibreIso K A U Y a y
  let e := p ≪≫ hcart.flip.isoPullback
  have he : e.hom ≫ pullback.fst f b = p.hom ≫ c := by
    change (p.hom ≫ hcart.flip.isoPullback.hom) ≫ pullback.fst f b = p.hom ≫ c
    rw [Category.assoc, hcart.flip.isoPullback_hom_fst]
  refine ⟨e, he, ?_, ?_⟩
  · change (p.hom ≫ hcart.flip.isoPullback.hom) ≫ pullback.snd f b = _
    rw [Category.assoc, hcart.flip.isoPullback_hom_snd]
    exact projectiveFibreIso_fst K A U Y a y
  · exact (congrArg (fun f ↦ f ≫ r) he).trans
      ((Category.assoc _ _ _).trans (congrArg (fun f ↦ p.hom ≫ f) hend))

private theorem coordinateRefinement (K : Type u) [CommRing K]
    {X : Scheme.{u}} (𝒲 : X.OpenCover.{u}) [Finite 𝒲.I₀]
    (A : 𝒲.I₀ → CommAlgCat.{u} K)
    (P : ∀ j, ((integralLineIntegerCocone (A j)).pt.left ≅ 𝒲.X j) → Prop)
    (hcoord : ∀ j, ∃ e : (integralLineIntegerCocone (A j)).pt.left ≅ 𝒲.X j, P j e) :
    ∃ e : ∀ j, (integralLineIntegerCocone (A j)).pt.left ≅ 𝒲.X j,
      (∀ j, P j (e j)) ∧
      ∃ 𝒱 : X.OpenCover.{u}, Finite 𝒱.I₀ ∧ (∀ k, IsAffine (𝒱.X k)) ∧
        ∃ (label : 𝒱.I₀ → 𝒲.I₀) (node : 𝒱.I₀ → ProjectiveLineIndex.{u})
          (d : ∀ k, Spec (.of ((FrobeniusSplitting.integerFibreDiagram (A (label k))
            (projectiveLineDiagram (ULift.{u} ℤ))).obj (node k))) ≅ 𝒱.X k),
          Function.Bijective (fun k : 𝒱.I₀ ↦
            (⟨label k, node k⟩ : Σ _ : 𝒲.I₀, ProjectiveLineIndex.{u})) ∧
          ∀ k, (d k).hom ≫ 𝒱.f k =
            ((integralLineIntegerCocone (A (label k))).ι.app (.op (node k))).left ≫
              (e (label k)).hom ≫ 𝒲.f (label k) := by
  classical
  choose e he using hcoord
  exact ⟨e, he, exists_integerBundleCover K 𝒲 A e⟩

end SchubertGeometry
