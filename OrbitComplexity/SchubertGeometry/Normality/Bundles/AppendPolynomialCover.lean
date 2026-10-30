import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveBundleData
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Charts
import Batteries.Tactic.Lint

/-! # Polynomial covers of projective append models

The two polynomial charts of every projective-line node give a finite affine
cover of its colimit. The cover retains the projection to the prior model
and the scalar comparison of each polynomial chart.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions

namespace SchubertGeometry

universe u

private theorem polynomial_chart_covers (A : Type u) [CommRing A]
    (x : projectiveScheme A (ULift.{u} (Fin 2))) :
    ∃ (j : ULift.{u} (Fin 2)) (y : Spec (.of (Polynomial A))),
      projectiveLinePolynomialChart A j y = x := by
  obtain ⟨j, z, hz⟩ := (projectiveChartCover A (ULift.{u} (Fin 2))).exists_eq x
  let j0 : ULift.{u} (Fin 2) := j
  have hz0 : x ∈ (projectiveChartMap A (ULift.{u} (Fin 2)) j0).opensRange := ⟨z, hz⟩
  have he : (projectiveLinePolynomialChart A j0).opensRange =
      (projectiveChartMap A (ULift.{u} (Fin 2)) j0).opensRange :=
    (projectiveLinePolynomialChart_range A j0).trans
      (projectiveChartMap_range A (ULift.{u} (Fin 2)) j0).symm
  have hx : x ∈ (projectiveLinePolynomialChart A j0).opensRange :=
    Eq.mp (congrArg (fun U : (projectiveScheme A (ULift.{u} (Fin 2))).Opens => x ∈ U)
      he.symm) hz0
  exact ⟨j0, hx⟩

private theorem diagram_chart_covers {I : Type u}
    (D : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ Scheme.{u}) (cD : Cocone D)
    (hc : ∀ (T : Scheme.{u}) (f : T ⟶ cD.pt) (y : T),
      ∃ s, ∃ z : (pullback f (cD.ι.app s) : Scheme.{u}),
        (pullback.fst f (cD.ι.app s)) z = y) (y : cD.pt) :
    ∃ (s : {s : Finset I // s.Nonempty}) (z : D.obj (op s)),
      cD.ι.app (op s) z = y := by
  obtain ⟨s, z, hz⟩ := hc cD.pt (𝟙 cD.pt) y
  have hmap : pullback.snd (𝟙 cD.pt) (cD.ι.app s) ≫ cD.ι.app s =
      pullback.fst (𝟙 cD.pt) (cD.ι.app s) :=
    pullback.condition.symm.trans (Category.comp_id _)
  exact ⟨s.unop, pullback.snd (𝟙 cD.pt) (cD.ι.app s) z,
    (congrArg (fun a => a z) hmap).trans hz⟩

private theorem chart_point_image {A B P Y : Scheme.{u}} (E : A ≅ B)
    (f : P ⟶ B) (a : A ⟶ Y) (z : A) (w : P) (h : f w = E.hom z) :
    (f ≫ E.inv ≫ a) w = a z := by
  change a (E.inv (f w)) = a z
  exact (congrArg (fun x => a (E.inv x)) h).trans
    (congrArg a (congrArg (fun k => k z) E.hom_inv_id))

section Cover

variable {I R : Type u} [CommRing R]
  (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
  (D : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
  (eP : ∀ s, D.obj (op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
  (cD : Cocone D)
  (ho : ∀ s, IsOpenImmersion (cD.ι.app s))
  (hc : ∀ (T : Scheme.{u}) (f : T ⟶ cD.pt) (y : T),
    ∃ s, ∃ z : (pullback f (cD.ι.app s) : Scheme.{u}),
      (pullback.fst f (cD.ι.app s)) z = y)

/-- The two polynomial charts of each projective node cover the append
colimit, with the coefficient-polynomial spectra as their domains. -/
def appendPolynomialCover : cD.pt.OpenCover.{u} :=
  Scheme.Cover.mkOfCovers
    ({s : Finset I // s.Nonempty} × ULift.{u} (Fin 2))
    (fun a => Spec (.of (Polynomial (N.obj a.1))))
    (fun a => projectiveLinePolynomialChart (N.obj a.1) a.2 ≫
      (eP a.1).inv ≫ cD.ι.app (op a.1))
    (fun y => by
      obtain ⟨s, z, hz⟩ := diagram_chart_covers D cD hc y
      obtain ⟨j, w, hw⟩ := polynomial_chart_covers (N.obj s) ((eP s).hom z)
      exact ⟨(s, j), w, (chart_point_image (eP s) _ _ z w hw).trans hz⟩)
    (fun a => by
      let : IsOpenImmersion (cD.ι.app (op a.1)) := ho (op a.1)
      infer_instance)

/-- A finite node family gives a finite polynomial cover. -/
instance appendPolynomialCover_finite [Finite I] :
    Finite (appendPolynomialCover N D eP cD ho hc).I₀ :=
  inferInstanceAs (Finite ({s : Finset I // s.Nonempty} × ULift.{u} (Fin 2)))

/-- Every chart of the polynomial append cover is affine. -/
instance appendPolynomialCover_affine
    (a : (appendPolynomialCover N D eP cD ho hc).I₀) :
    IsAffine ((appendPolynomialCover N D eP cD ho hc).X a) :=
  inferInstanceAs (IsAffine (Spec (.of (Polynomial (N.obj a.1)))))

/-- Each cover arrow is the prescribed polynomial chart followed by the node
isomorphism and the original colimit leg. -/
theorem appendPolynomialCover_map (s : {s : Finset I // s.Nonempty})
    (j : ULift.{u} (Fin 2)) :
    (appendPolynomialCover N D eP cD ho hc).f (s, j) =
      projectiveLinePolynomialChart (N.obj s) j ≫ (eP s).inv ≫ cD.ι.app (op s) := rfl

end Cover

private theorem chart_projection {A B P S X Y : Scheme.{u}}
    (E : A ≅ B) (f : P ⟶ B) (p : B ⟶ S) (π : A ⟶ S)
    (a : A ⟶ X) (q : X ⟶ Y) (b : S ⟶ Y)
    (hπ : π = E.hom ≫ p) (ha : a ≫ q = π ≫ b) :
    (f ≫ E.inv ≫ a) ≫ q = (f ≫ p) ≫ b := by
  calc
    (f ≫ E.inv ≫ a) ≫ q = f ≫ E.inv ≫ (a ≫ q) := by simp only [Category.assoc]
    _ = f ≫ E.inv ≫ (π ≫ b) := congrArg (fun k => f ≫ E.inv ≫ k) ha
    _ = f ≫ E.inv ≫ ((E.hom ≫ p) ≫ b) :=
      congrArg (fun k => f ≫ E.inv ≫ (k ≫ b)) hπ
    _ = (f ≫ p) ≫ b := by simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The cover charts preserve the projection to the same prior coefficient
cocone. -/
theorem appendPolynomialCover_projection {I R : Type u} [CommRing R]
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (D : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
    (eP : ∀ s, D.obj (op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
    (cD : Cocone D) (ho : ∀ s, IsOpenImmersion (cD.ι.app s))
    (hc : ∀ (T : Scheme.{u}) (f : T ⟶ cD.pt) (y : T),
      ∃ s, ∃ z : (pullback f (cD.ι.app s) : Scheme.{u}),
        (pullback.fst f (cD.ι.app s)) z = y)
    (cG : Cocone (N.op ⋙ algSpec (.of R))) (q : cD.pt ⟶ cG.pt.left)
    (π : D ⟶ N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)))
    (hπ : ∀ s, π.app (op s) = (eP s).hom ≫
      projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)))
    (hq : ∀ s, cD.ι.app s ≫ q = π.app s ≫ (cG.ι.app s).left)
    (s : {s : Finset I // s.Nonempty}) (j : ULift.{u} (Fin 2)) :
    (appendPolynomialCover N D eP cD ho hc).f (s, j) ≫ q =
      Spec.map (CommRingCat.ofHom (Polynomial.C : N.obj s →+* Polynomial (N.obj s))) ≫
        (cG.ι.app (op s)).left := by
  exact (congrArg (fun k => k ≫ q) (appendPolynomialCover_map N D eP cD ho hc s j)).trans
    ((chart_projection (eP s) (projectiveLinePolynomialChart (N.obj s) j)
      (projectiveToSpec (N.obj s) (ULift.{u} (Fin 2))) (π.app (op s))
      (cD.ι.app (op s)) q (cG.ι.app (op s)).left (hπ s) (hq (op s))).trans
      (congrArg (fun k => k ≫ (cG.ι.app (op s)).left)
        (projectiveLinePolynomialChart_base (N.obj s) j)))

/-- A polynomial-chart scalar square is unchanged when its arithmetic arrow
is expressed as a chart of the append cover. -/
theorem appendPolynomialCover_scalar {I R K : Type u} [CommRing R] [CommRing K]
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (D : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
    (eP : ∀ s, D.obj (op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
    (cD : Cocone D) (ho : ∀ s, IsOpenImmersion (cD.ι.app s))
    (hc : ∀ (T : Scheme.{u}) (f : T ⟶ cD.pt) (y : T),
      ∃ s, ∃ z : (pullback f (cD.ι.app s) : Scheme.{u}),
        (pullback.fst f (cD.ι.app s)) z = y)
    (v : ∀ s, N.obj s →+* F.obj s) {X : Scheme.{u}} (m : X ⟶ cD.pt)
    (a : ∀ s, ULift.{u} (Fin 2) → (Spec (.of (Polynomial (F.obj s))) ⟶ X))
    (hm : ∀ s j, a s j ≫ m =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (v s))) ≫
        (projectiveLinePolynomialChart (N.obj s) j ≫ (eP s).inv ≫ cD.ι.app (op s)))
    (s : {s : Finset I // s.Nonempty}) (j : ULift.{u} (Fin 2)) :
    a s j ≫ m = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (v s))) ≫
      (appendPolynomialCover N D eP cD ho hc).f (s, j) :=
  (hm s j).trans (congrArg
    (fun k => Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (v s))) ≫ k)
    (appendPolynomialCover_map N D eP cD ho hc s j).symm)

end SchubertGeometry
