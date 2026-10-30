import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition
import TauCeti.AlgebraicGeometry.Modules.Pullback

/-! # Pullback maps on the specified trivialized chart of the projective line module -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open CategoryTheory AlgebraicGeometry GroupActions
universe u

private abbrev structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- A chart trivialization transports the canonical pullback of the structure sheaf. -/
def trivializedPullbackIso {X : Scheme.{u}} (M : X.Modules)
    (e : M ≅ structureModule X) (f : X ⟶ X) (a : Γ(X, ⊤)ˣ) :
    (Scheme.Modules.pullback f).obj M ≅ M :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ Scheme.Modules.pullbackObjUnitIso f ≪≫
    asIso (Scheme.Modules.globalSectionsSmul (structureModule X) (a : Γ(X, ⊤))) ≪≫ e.symm

/-- The pullback isomorphism has the specified multiplier in the given chart. -/
theorem trivializedPullbackIso_chart {X : Scheme.{u}} (M : X.Modules)
    (e : M ≅ structureModule X) (f : X ⟶ X) (a : Γ(X, ⊤)ˣ) :
    (trivializedPullbackIso M e f a).hom ≫ e.hom =
      (Scheme.Modules.pullback f).map e.hom ≫
        (Scheme.Modules.pullbackObjUnitIso f).hom ≫
          Scheme.Modules.globalSectionsSmul (structureModule X) (a : Γ(X, ⊤)) := by
  simp only [trivializedPullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The identity coordinate change has the canonical identity pullback map. -/
theorem trivializedPullbackIso_id {X : Scheme.{u}} (M : X.Modules)
    (e : M ≅ structureModule X) :
    (trivializedPullbackIso M e (𝟙 X) 1).hom =
      (Scheme.Modules.pullbackId X).hom.app M := by
  apply (cancel_mono e.hom).mp
  calc
    _ = (Scheme.Modules.pullback (𝟙 X)).map e.hom ≫
        (Scheme.Modules.pullbackObjUnitIso (𝟙 X)).hom ≫
          Scheme.Modules.globalSectionsSmul (structureModule X) (1 : Γ(X, ⊤)) :=
      trivializedPullbackIso_chart M e (𝟙 X) 1
    _ = (Scheme.Modules.pullback (𝟙 X)).map e.hom ≫
        (Scheme.Modules.pullbackObjUnitIso (𝟙 X)).hom := by
      rw [Scheme.Modules.globalSectionsSmul_one]
      exact congrArg (fun v => (Scheme.Modules.pullback (𝟙 X)).map e.hom ≫ v)
        (Category.comp_id (Scheme.Modules.pullbackObjUnitIso (𝟙 X)).hom)
    _ = (Scheme.Modules.pullback (𝟙 X)).map e.hom ≫
        (Scheme.Modules.pullbackId X).hom.app (structureModule X) := by
      rw [Scheme.Modules.pullbackObjUnitIso_id]
      rfl
    _ = _ := (Scheme.Modules.pullbackId X).hom.naturality e.hom

/-- These sheaf pullback maps obey the composition law with pulled-back scalars. -/
theorem trivializedPullbackIso_comp {X : Scheme.{u}} (M : X.Modules)
    (e : M ≅ structureModule X) (f g : X ⟶ X) (a b : Γ(X, ⊤)ˣ) :
    (Scheme.Modules.pullbackComp f g).inv.app M ≫
        (Scheme.Modules.pullback f).map (trivializedPullbackIso M e g b).hom ≫
          (trivializedPullbackIso M e f a).hom =
      (trivializedPullbackIso M e (f ≫ g)
        (a * Units.map f.appTop.hom b)).hom := by
  let F := Scheme.Modules.pullback f
  let G := Scheme.Modules.pullback g
  let H := Scheme.Modules.pullback (f ≫ g)
  let P := Scheme.Modules.pullbackComp f g
  let O := structureModule X
  let U := Scheme.Modules.pullbackObjUnitIso f
  let V := Scheme.Modules.pullbackObjUnitIso g
  let W := Scheme.Modules.pullbackObjUnitIso (f ≫ g)
  let A := Scheme.Modules.globalSectionsSmul O (a : Γ(X, ⊤))
  let B := Scheme.Modules.globalSectionsSmul O (b : Γ(X, ⊤))
  let C := Scheme.Modules.globalSectionsSmul O (f.appTop (b : Γ(X, ⊤)))
  have hF : F.map (trivializedPullbackIso M e g b).hom ≫ F.map e.hom =
      F.map (G.map e.hom ≫ V.hom ≫ B) := by
    rw [← F.map_comp, trivializedPullbackIso_chart]
  have hS : F.map B ≫ U.hom = U.hom ≫ C := by
    change (Scheme.Modules.pullback f).map
      (Scheme.Modules.globalSectionsSmul O (b : Γ(X, ⊤))) ≫ U.hom = _
    rw [Scheme.Modules.pullback_map_globalSectionsSmul]
    exact Scheme.Modules.globalSectionsSmul_naturality U.hom _
  have hN : P.inv.app M ≫ F.map (G.map e.hom) = H.map e.hom ≫ P.inv.app O :=
    (P.inv.naturality e.hom).symm
  have hU : P.inv.app O ≫ F.map V.hom ≫ U.hom = W.hom :=
    Scheme.Modules.pullbackObjUnitIso_comp f g
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, trivializedPullbackIso_chart]
  change P.inv.app M ≫ F.map (trivializedPullbackIso M e g b).hom ≫
      F.map e.hom ≫ U.hom ≫ A =
    H.map e.hom ≫ W.hom ≫
      Scheme.Modules.globalSectionsSmul O ((a : Γ(X, ⊤)) * f.appTop (b : Γ(X, ⊤)))
  calc
    _ = P.inv.app M ≫
        (F.map (trivializedPullbackIso M e g b).hom ≫ F.map e.hom) ≫ U.hom ≫ A := by
      simp only [Category.assoc]
    _ = P.inv.app M ≫ F.map (G.map e.hom ≫ V.hom ≫ B) ≫ U.hom ≫ A := by rw [hF]
    _ = (P.inv.app M ≫ F.map (G.map e.hom)) ≫ F.map V.hom ≫
        (F.map B ≫ U.hom) ≫ A := by simp only [Functor.map_comp, Category.assoc]
    _ = H.map e.hom ≫ (P.inv.app O ≫ F.map V.hom ≫ U.hom) ≫ C ≫ A := by
      rw [hN, hS]
      simp only [Category.assoc]
    _ = H.map e.hom ≫ W.hom ≫ C ≫ A := by rw [hU]
    _ = _ := by rw [Scheme.Modules.globalSectionsSmul_mul]

/-- The first Laurent-transition chart has a specified sheaf pullback isomorphism. -/
def projectiveChartPullbackIso (C : Type u) [CommRing C] (d : ℕ)
    (f : Spec (.of (Polynomial C)) ⟶ Spec (.of (Polynomial C)))
    (a : Γ(Spec (.of (Polynomial C)), ⊤)ˣ) :
    (Scheme.Modules.pullback f).obj
        ((SchubertGeometry.ProjectiveLine.projectiveTransitionModule C d).restrict
          (projectiveLinePolynomialChart C ⟨0⟩)) ≅
      (SchubertGeometry.ProjectiveLine.projectiveTransitionModule C d).restrict
        (projectiveLinePolynomialChart C ⟨0⟩) :=
  trivializedPullbackIso _ (SchubertGeometry.ProjectiveLine.projectiveTransitionChart C d ⟨0⟩) f a

end SchubertGeometry.ProjectiveLine
