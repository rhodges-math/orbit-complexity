import OrbitComplexity.SchubertGeometry.Normality.Transitions.TransitionData
import OrbitComplexity.SchubertGeometry.Normality.Models.AffineComposition
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.AffineFamilies

/-! # Equifibered projective-line diagrams from affine transition coefficients -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions
noncomputable section
universe u v
namespace SchubertGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

private def affineIso {R : Type u} [CommRing R] (c : Rˣ) (a : R) :
    projectiveScheme R (ULift.{u} (Fin 2)) ≅ projectiveScheme R (ULift.{u} (Fin 2)) :=
  projectiveLineScalingIso c ≪≫ projectiveLineTranslationIso a

private theorem affine_base {R : Type u} [CommRing R] (c : Rˣ) (a : R) :
    (affineIso c a).hom ≫ projectiveToSpec R (ULift.{u} (Fin 2)) =
      projectiveToSpec R (ULift.{u} (Fin 2)) := by
  simp only [affineIso, Iso.trans_hom, Category.assoc,
    projectiveLineTranslation_base, projectiveLineScaling_base]

private theorem affine_coeff {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (c : Rˣ) (a : R) :
    (affineIso (Units.map f.toMonoidHom c) (f a)).hom ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      projectiveCoeffMap (ULift.{u} (Fin 2)) f ≫ (affineIso c a).hom :=
  projectiveAffine_coeff f c a

private theorem affine_laws {R : Type u} [CommRing R] {J : Type v}
    (c : J → J → Rˣ) (a : J → J → R)
    (h : ∀ j k l, c j l = c k l * c j k ∧ a j l = (c k l : R) * a j k + a k l) :
    (∀ j, (affineIso (c j j) (a j j)).hom = 𝟙 _) ∧
    ∀ j k l, (affineIso (c j k) (a j k)).hom ≫
      (affineIso (c k l) (a k l)).hom = (affineIso (c j l) (a j l)).hom := by
  have hc (j : J) : c j j = 1 := by
    apply mul_left_cancel (a := c j j)
    simpa only [mul_one] using (h j j j).1.symm
  have ha (j : J) : a j j = 0 := by
    have hh := (h j j j).2
    rw [hc, Units.val_one, one_mul] at hh
    exact add_left_cancel (show a j j + a j j = a j j + 0 by simpa using hh.symm)
  refine ⟨fun j ↦ ?_, fun j k l ↦ ?_⟩
  · simpa only [affineIso, Iso.trans_hom, hc, ha] using projectiveAffine_one (R := R)
  · simpa only [affineIso, Iso.trans_hom, ← (h j k l).1, ← (h j k l).2] using
      projectiveAffine_comp (c j k) (c k l) (a j k) (a k l)

private theorem coefficient_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) g ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      projectiveCoeffMap (ULift.{u} (Fin 2)) (g.comp f) := by
  unfold projectiveCoeffMap
  rw [← Proj.map_comp]
  congr 1
  apply GradedRingHom.toRingHom_injective
  change (MvPolynomial.map g).comp (MvPolynomial.map f) = MvPolynomial.map (g.comp f)
  apply MvPolynomial.ringHom_ext <;> intro x <;> simp

private theorem coefficient_id {R : Type u} [CommRing R] :
    projectiveCoeffMap (ULift.{u} (Fin 2)) (RingHom.id R) = 𝟙 _ := by
  unfold projectiveCoeffMap
  rw [← Proj.map_id]
  congr 1
  apply GradedRingHom.toRingHom_injective
  change MvPolynomial.map (RingHom.id R) = RingHom.id _
  apply MvPolynomial.ringHom_ext <;> intro x <;> simp

private theorem coefficient_base {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) f ≫ projectiveToSpec R (ULift.{u} (Fin 2)) =
      projectiveToSpec S (ULift.{u} (Fin 2)) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← projectiveBaseChange_snd (ULift.{u} (Fin 2)) f, Category.assoc,
    ← pullback.condition, ← Category.assoc, projectiveBaseChange_fst]

private theorem affine_pullback {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (c : Sˣ) (a : S) :
    IsPullback ((affineIso c a).hom ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f)
      (projectiveToSpec S (ULift.{u} (Fin 2)))
      (projectiveToSpec R (ULift.{u} (Fin 2))) (Spec.map (CommRingCat.ofHom f)) := by
  have h : IsPullback (projectiveToSpec S (ULift.{u} (Fin 2)))
      (projectiveCoeffMap (ULift.{u} (Fin 2)) f) (Spec.map (CommRingCat.ofHom f))
      (projectiveToSpec R (ULift.{u} (Fin 2))) :=
    IsPullback.of_iso_pullback ⟨(coefficient_base f).symm⟩
      (projectiveBaseChange (ULift.{u} (Fin 2)) f)
      (projectiveBaseChange_fst _ f) (projectiveBaseChange_snd _ f)
  apply h.flip.of_iso' (affineIso c a) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simpa using affine_base c a
  · simp
  · simp

variable {I R : Type u} [CommRing R]
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (N.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), N.obj s)

private def transition {s t : {s : Finset I // s.Nonempty}} (f : s ⟶ t) :
    projectiveScheme (N.obj t) (ULift.{u} (Fin 2)) ⟶
      projectiveScheme (N.obj s) (ULift.{u} (Fin 2)) :=
  (affineIso (c t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))
    (a t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))).hom ≫
    projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map f).hom.toRingHom

variable
    (hco : ∀ (s : {s : Finset I // s.Nonempty}) j hj k hk l hl,
      c s j hj l hl = c s k hk l hl * c s j hj k hk ∧
      a s j hj l hl = (c s k hk l hl : N.obj s) * a s j hj k hk + a s k hk l hl)
    (hn : ∀ (s t : {s : Finset I // s.Nonempty}) (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toRingHom.toMonoidHom (c s j hj k hk) =
        c t j ((leOfHom f) hj) k ((leOfHom f) hk) ∧
      (N.map f).hom (a s j hj k hk) = a t j ((leOfHom f) hj) k ((leOfHom f) hk))

include hco in
private theorem transition_id (s : {s : Finset I // s.Nonempty}) :
    transition N sel c a (𝟙 s) = 𝟙 _ := by
  have hid := (affine_laws
    (fun j k : {j : I // j ∈ s.val} ↦ c s j.val j.property k.val k.property)
    (fun j k : {j : I // j ∈ s.val} ↦ a s j.val j.property k.val k.property)
    (fun j k l ↦ hco s j.val j.property k.val k.property l.val l.property)).1 (sel s)
  unfold transition
  rw [N.map_id, hid, Category.id_comp]
  exact coefficient_id

include hco hn in
private theorem transition_comp {s t r : {s : Finset I // s.Nonempty}}
    (f : s ⟶ t) (g : t ⟶ r) :
    transition N sel c a (f ≫ g) = transition N sel c a g ≫ transition N sel c a f := by
  have hnat := hn t r g (sel t).val (sel t).property
    (sel s).val ((leOfHom f) (sel s).property)
  have hcomp := (affine_laws
    (fun j k : {j : I // j ∈ r.val} ↦ c r j.val j.property k.val k.property)
    (fun j k : {j : I // j ∈ r.val} ↦ a r j.val j.property k.val k.property)
    (fun j k l ↦ hco r j.val j.property k.val k.property l.val l.property)).2
      (sel r) ⟨(sel t).val, (leOfHom g) (sel t).property⟩
      ⟨(sel s).val, (leOfHom g) ((leOfHom f) (sel s).property)⟩
  let P := affineIso
    (c r (sel r).val (sel r).property (sel t).val ((leOfHom g) (sel t).property))
    (a r (sel r).val (sel r).property (sel t).val ((leOfHom g) (sel t).property))
  let Q := affineIso
    (c t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))
    (a t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))
  let Q' := affineIso
    (c r (sel t).val ((leOfHom g) (sel t).property)
      (sel s).val ((leOfHom g) ((leOfHom f) (sel s).property)))
    (a r (sel t).val ((leOfHom g) (sel t).property)
      (sel s).val ((leOfHom g) ((leOfHom f) (sel s).property)))
  let U := affineIso
    (c r (sel r).val (sel r).property (sel s).val ((leOfHom (f ≫ g)) (sel s).property))
    (a r (sel r).val (sel r).property (sel s).val ((leOfHom (f ≫ g)) (sel s).property))
  let pg := (N.map g).hom.toRingHom
  let pf := (N.map f).hom.toRingHom
  have hcg : Units.map pg.toMonoidHom
      (c t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property)) =
      c r (sel t).val ((leOfHom g) (sel t).property)
        (sel s).val ((leOfHom g) ((leOfHom f) (sel s).property)) := hnat.1
  have hag : pg
      (a t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property)) =
      a r (sel t).val ((leOfHom g) (sel t).property)
        (sel s).val ((leOfHom g) ((leOfHom f) (sel s).property)) := hnat.2
  have hcoeff : projectiveCoeffMap (ULift.{u} (Fin 2)) pg ≫ Q.hom =
      Q'.hom ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) pg := by
    simpa only [Q, Q', hcg, hag] using
      (affine_coeff pg
        (c t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))
        (a t (sel t).val (sel t).property (sel s).val ((leOfHom f) (sel s).property))).symm
  change P.hom ≫ Q'.hom = U.hom at hcomp
  change U.hom ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) (N.map (f ≫ g)).hom.toRingHom =
    (P.hom ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) pg) ≫
      (Q.hom ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) pf)
  rw [N.map_comp]
  change U.hom ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) (pg.comp pf) = _
  symm
  calc
    _ = P.hom ≫ (projectiveCoeffMap (ULift.{u} (Fin 2)) pg ≫ Q.hom) ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) pf := by simp only [Category.assoc]
    _ = P.hom ≫ (Q'.hom ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) pg) ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) pf := by rw [hcoeff]
    _ = (P.hom ≫ Q'.hom) ≫ (projectiveCoeffMap (ULift.{u} (Fin 2)) pg ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) pf) := by simp only [Category.assoc]
    _ = _ := by rw [hcomp, coefficient_comp]

private theorem transition_base {s t : {s : Finset I // s.Nonempty}} (f : s ⟶ t) :
    transition N sel c a f ≫ projectiveToSpec (N.obj s) (ULift.{u} (Fin 2)) =
      projectiveToSpec (N.obj t) (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom) := by
  unfold transition
  rw [Category.assoc, coefficient_base, ← Category.assoc, affine_base]

include hco hn in
private def transitionDiagram : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ Scheme.{u} where
  obj s := projectiveScheme (N.obj s.unop) (ULift.{u} (Fin 2))
  map f := transition N sel c a f.unop
  map_id s := transition_id N sel c a hco s.unop
  map_comp f g := transition_comp N sel c a hco hn g.unop f.unop

private def transitionProjection : transitionDiagram N sel c a hco hn ⟶
    N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R)) where
  app s := projectiveToSpec (N.obj s.unop) (ULift.{u} (Fin 2))
  naturality s t f := by
    change transition N sel c a f.unop ≫
        projectiveToSpec (N.obj t.unop) (ULift.{u} (Fin 2)) =
      projectiveToSpec (N.obj s.unop) (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (N.map f.unop).hom.toRingHom)
    exact transition_base N sel c a f.unop

private theorem projection_cartesian :
    (transitionProjection N sel c a hco hn).Equifibered := by
  intro s t f
  exact affine_pullback (N.map f.unop).hom.toRingHom _ _

include hco hn in
/-- Affine cocycles construct the projective diagram and its cartesian coefficient projection. -/
theorem exists_projective_transition : projectiveTransitionSpec N sel c a := by
  refine ⟨transitionDiagram N sel c a hco hn, fun _ ↦ Iso.refl _,
    transitionProjection N sel c a hco hn, ?_, ?_, projection_cartesian N sel c a hco hn⟩
  · intro s
    exact (Category.id_comp _).symm
  · intro s t f
    simp only [Iso.refl_hom]
    rfl

end SchubertGeometry
