import OrbitComplexity.SchubertGeometry.ProjectiveLine.PolynomialChart
import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedMaps
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange
import OrbitComplexity.SchubertGeometry.Parabolics.CurveFibre
import OrbitComplexity.SchubertGeometry.Normality.Curves.ClosedCurveComparison
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian

/-!
# Retaining global projective maps into the same chosen target

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions

open FrobeniusSplitting ReductiveGroups

noncomputable section

namespace SchubertGeometry

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem reparametrize_retained_square
    {C : Type*} [Category C] {A B X Y : C} (e : A ≅ B)
    (q : X ⟶ B) (f : B ⟶ Y) (k : X ⟶ Y) (h : q ≫ f = k) :
    (q ≫ e.inv) ≫ (e.hom ≫ f) = k := by
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

variable {K : Type u} [CommRing K] (S : Subalgebra ℤ K)

/-- The specified canonical projective model has its prescribed generic fibre
as an isomorphism over the original coefficient field. -/
def projectiveGenericIso (ι : Type u) [Finite ι] :
    Over.mk (projectiveToSpec K ι) ≅ genericScalarModel S (projectiveToSpec S ι) :=
  Over.isoMk (projectiveBaseChange ι (algebraMap S K))
    (projectiveBaseChange_fst ι (algebraMap S K))

/-- The specified canonical projective model at a later stage is the scalar
extension of the same original projective model, over that stage's base. -/
def projectiveStageIso (ι : Type u) [Finite ι] (j : CoefficientStage S) :
    Over.mk (projectiveToSpec j.val ι) ≅ stageScalarModel S (projectiveToSpec S ι) j :=
  Over.isoMk (projectiveBaseChange ι (Subalgebra.inclusion j.property.2).toRingHom)
    (projectiveBaseChange_fst ι (Subalgebra.inclusion j.property.2).toRingHom)

/-- A specified Cartesian comparison identifies the original generic target
with the generic scalar pullback of the same coefficient model. -/
def cartesianGenericIso (D : Over (Spec (.of S))) (DK : Over (Spec (.of K)))
    (qD : DK.left ⟶ D.left)
    (hD : IsPullback qD DK.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    DK ≅ genericScalarModel S D.hom :=
  Over.isoMk hD.flip.isoPullback hD.flip.isoPullback_hom_fst

/-- Express a specified global generic projective map between the original
models, using only their canonical scalar and specified Cartesian comparisons. -/
def projectiveGenericMap (ι : Type u) [Finite ι]
    (D : Over (Spec (.of S))) (DK : Over (Spec (.of K)))
    (qD : DK.left ⟶ D.left)
    (hD : IsPullback qD DK.hom D.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (g : Over.mk (projectiveToSpec K ι) ⟶ DK) :
    genericScalarModel S (projectiveToSpec S ι) ⟶ genericScalarModel S D.hom :=
  (projectiveGenericIso S ι).inv ≫ g ≫ (cartesianGenericIso S D DK qD hD).hom

/-- Transport a Cartesian square along an isomorphism of its upper-left object. -/
theorem curveModel_pullback {T : Type*} [Category T]
    {P A F Q N : T} {f : P ⟶ A} {g : P ⟶ F}
    {a : A ⟶ Q} {π : F ⟶ Q} (h : IsPullback f g a π)
    (E : N ≅ P) (d : N ⟶ A) (n : N ⟶ F)
    (hd : E.hom ≫ f = d) (hn : E.hom ≫ g = n) :
    IsPullback d n a π :=
  h.of_iso' E (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (hd.trans (Category.comp_id d).symm) (hn.trans (Category.comp_id n).symm)
    ((Category.id_comp a).trans (Category.comp_id a).symm)
    ((Category.id_comp π).trans (Category.comp_id π).symm)

/-- A composite satisfies the triangle determined by its two factors. -/
theorem curveModel_composite_triangle {T : Type*} [Category T]
    {A B C D : T} (e : A ⟶ B) (p : B ⟶ C) (r : C ⟶ D)
    (q : B ⟶ D) (s : A ⟶ D) (hp : p ≫ r = q) (he : e ≫ q = s) :
    (e ≫ p) ≫ r = s :=
  (Category.assoc _ _ _).trans ((congrArg (fun f => e ≫ f) hp).trans he)

/-- The simple Schubert curve has its canonical projective coefficient model. -/
theorem curveModel_projective_square
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (G : ReductiveGroupData K) (i : G.rootBase.support) :
    IsPullback (simpleCurveCoefficientMap S G i)
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
      (projectiveToSpec S (ULift.{u} (Fin 2)))
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) := by
  let E := (Over.forget (Spec (.of K))).mapIso (simpleSchubertIso G i)
  let P := projectiveBaseChange (ULift.{u} (Fin 2)) (algebraMap S K)
  exact curveModel_pullback
    (IsPullback.of_hasPullback
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))
      (projectiveToSpec S (ULift.{u} (Fin 2)))).flip
    (E ≪≫ P) (simpleCurveCoefficientMap S G i) _
    (curveModel_composite_triangle E.hom P.hom _ _ _
      (projectiveBaseChange_snd (ULift.{u} (Fin 2)) (algebraMap S K)) rfl)
    (curveModel_composite_triangle E.hom P.hom _ _ _
      (projectiveBaseChange_fst (ULift.{u} (Fin 2)) (algebraMap S K))
      (simpleSchubertIso G i).hom.w)

/-- Projective coefficient morphisms respect composition of ring homomorphisms. -/
theorem projectiveCoefficient_composition
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) g ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f =
      projectiveCoeffMap (ULift.{u} (Fin 2)) (g.comp f) := by
  unfold projectiveCoeffMap
  rw [← Proj.map_comp]
  congr 1
  ext p m
  exact congrArg (fun q => AddMonoidAlgebra.coeff q m) (MvPolynomial.map_map f g p)

/-- Compatible projective coefficient maps satisfy the scalar-tower triangle. -/
theorem projectiveCoefficient_triangle
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (h : R →+* B) (hgf : g.comp f = h)
    {X Y : Scheme.{u}} (z : X ⟶ projectiveScheme B (ULift.{u} (Fin 2)))
    (l : projectiveScheme A (ULift.{u} (Fin 2)) ⟶ Y)
    (p : Y ⟶ projectiveScheme R (ULift.{u} (Fin 2)))
    (hp : l ≫ p = projectiveCoeffMap (ULift.{u} (Fin 2)) f)
    (qA : X ⟶ projectiveScheme A (ULift.{u} (Fin 2)))
    (qR : X ⟶ projectiveScheme R (ULift.{u} (Fin 2)))
    (ha : qA = z ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) g)
    (hr : qR = z ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) h) :
    (qA ≫ l) ≫ p = qR := by
  calc
    (qA ≫ l) ≫ p = qA ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f :=
      (Category.assoc _ _ _).trans (congrArg (fun k => qA ≫ k) hp)
    _ = (z ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) g) ≫
        projectiveCoeffMap (ULift.{u} (Fin 2)) f :=
      congrArg (fun k => k ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) f) ha
    _ = z ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) (g.comp f) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun k => z ≫ k) (projectiveCoefficient_composition f g))
    _ = z ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) h :=
      congrArg (fun k => z ≫ projectiveCoeffMap (ULift.{u} (Fin 2)) k) hgf
    _ = qR := hr.symm

/-- The canonical projection from the generic fibre to a coefficient-stage model. -/
def genericLeg {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {I : Scheme.{u}} (b : I ⟶ Spec (.of S)) (k : CoefficientStage S) :
    (genericScalarModel S b).left ⟶ (stageScalarModel S b k).left :=
  (modelScalarCone S b).π.app (op k)

/-- The coefficient-stage projection retains its original generic projection. -/
theorem genericLeg_projection {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {I : Scheme.{u}} (b : I ⟶ Spec (.of S)) (k : CoefficientStage S) :
    genericLeg S b k ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) b =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) b := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  exact pullback.lift_snd _ _ _

/-- The coefficient-stage map determined by a specified Cartesian generic fibre. -/
def modelStageMap {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X XK : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : XK ⟶ Spec (.of K))
    (q : XK ⟶ X) (h : IsPullback q b a (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (k : CoefficientStage S) : XK ⟶ (stageScalarModel S a k).left :=
  h.flip.isoOverPullback.hom.left ≫ genericLeg S a k

/-- The coefficient-stage map of a Cartesian generic fibre is Cartesian. -/
theorem modelStageMap_cartesian {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X XK : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : XK ⟶ Spec (.of K))
    (q : XK ⟶ X) (h : IsPullback q b a (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (k : CoefficientStage S) :
    IsPullback (modelStageMap S a b q h k) b (stageScalarModel S a k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
  overIso_modelStage_cartesian S a k (Over.mk b) h.flip.isoOverPullback

/-- The coefficient-stage map retains its specified original projection. -/
theorem modelStageMap_projection {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {X XK : Scheme.{u}} (a : X ⟶ Spec (.of S)) (b : XK ⟶ Spec (.of K))
    (q : XK ⟶ X) (h : IsPullback q b a (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (k : CoefficientStage S) :
    modelStageMap S a b q h k ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) a = q :=
  curveModel_composite_triangle h.flip.isoOverPullback.hom.left (genericLeg S a k) _ _ q
    (genericLeg_projection S a k) h.flip.isoOverPullback_hom_left_comp_snd

/-- Maps into Cartesian models agree when their two projections agree. -/
theorem modelStageMap_eq_of_projections {T : Type*} [Category T]
    {X Y X₀ Y₀ B BK X₁ Y₁ B₁ : T}
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (pX : X ⟶ X₀) (pY : Y ⟶ Y₀)
    (bX : X ⟶ BK) (bY : Y ⟶ BK) (qX : X ⟶ X₁) (qY : Y ⟶ Y₁)
    (PX : X₁ ⟶ X₀) (PY : Y₁ ⟶ Y₀) (aX : X₁ ⟶ B₁) (aY : Y₁ ⟶ B₁)
    (y : Y₀ ⟶ B) (κ₀ : B₁ ⟶ B) (hY : IsPullback PY aY y κ₀)
    (f₁ : X₁ ⟶ Y₁) (κ : BK ⟶ B₁)
    (hXo : qX ≫ PX = pX) (hYo : qY ≫ PY = pY)
    (hfo : f₁ ≫ PY = PX ≫ f₀) (hfb : f₁ ≫ aY = aX)
    (hXb : qX ≫ aX = bX ≫ κ) (hYb : qY ≫ aY = bY ≫ κ)
    (hnb : f ≫ bY = bX) (hcomm : pX ≫ f₀ = f ≫ pY) :
    qX ≫ f₁ = f ≫ qY := by
  apply hY.hom_ext
  · calc
      (qX ≫ f₁) ≫ PY = qX ≫ (PX ≫ f₀) :=
        (Category.assoc _ _ _).trans (congrArg (fun k => qX ≫ k) hfo)
      _ = pX ≫ f₀ := (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ f₀) hXo)
      _ = f ≫ pY := hcomm
      _ = (f ≫ qY) ≫ PY :=
        (congrArg (fun k => f ≫ k) hYo.symm).trans (Category.assoc _ _ _).symm
  · calc
      (qX ≫ f₁) ≫ aY = qX ≫ aX :=
        (Category.assoc _ _ _).trans (congrArg (fun k => qX ≫ k) hfb)
      _ = bX ≫ κ := hXb
      _ = (f ≫ bY) ≫ κ := congrArg (fun k => k ≫ κ) hnb.symm
      _ = (f ≫ qY) ≫ aY :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun k => f ≫ k) hYb.symm).trans (Category.assoc _ _ _).symm)

/-- Coefficient-stage maps respect a specified morphism of generic fibres. -/
theorem modelStageMap_naturality
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {XK YK : Over (Spec (.of K))} {X Y : Over (Spec (.of S))}
    (fK : XK ⟶ YK) (f : X ⟶ Y)
    (qX : XK.left ⟶ X.left) (qY : YK.left ⟶ Y.left)
    (hX : IsPullback qX XK.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hY : IsPullback qY YK.hom Y.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hf : qX ≫ f.left = fK.left ≫ qY) (k : CoefficientStage S) :
    modelStageMap S X.hom XK.hom qX hX k ≫
        (chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) f).left =
      fK.left ≫ modelStageMap S Y.hom YK.hom qY hY k := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
  exact modelStageMap_eq_of_projections fK.left f.left qX qY XK.hom YK.hom
    (modelStageMap S X.hom XK.hom qX hX k) (modelStageMap S Y.hom YK.hom qY hY k)
    (pullback.snd κ X.hom) (pullback.snd κ Y.hom)
    (stageScalarModel S X.hom k).hom (stageScalarModel S Y.hom k).hom Y.hom κ
    (IsPullback.of_hasPullback κ Y.hom).flip (chosenScalarArrow κ f).left
    (Spec.map (CommRingCat.ofHom (algebraMap k.val K)))
    (modelStageMap_projection S X.hom XK.hom qX hX k)
    (modelStageMap_projection S Y.hom YK.hom qY hY k)
    (chosenScalarArrow_snd κ f) (chosenScalarArrow κ f).w
    (modelStageMap_cartesian S X.hom XK.hom qX hX k).w
    (modelStageMap_cartesian S Y.hom YK.hom qY hY k).w fK.w hf

/-- The simple-curve coefficient map agrees with its projective stage model. -/
theorem projectiveStage_coefficient_agreement
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (G : ReductiveGroupData K) (i : G.rootBase.support)
    (k : CoefficientStage S) :
    let h := curveModel_projective_square S G i
    let E := h.flip.isoOverPullback
    simpleCurveCoefficientMap k.val G i ≫ (projectiveStageIso S (ULift.{u} (Fin 2)) k).hom.left =
      E.hom.left ≫ genericLeg S (projectiveToSpec S (ULift.{u} (Fin 2))) k := by
  intro h E
  let a := projectiveToSpec S (ULift.{u} (Fin 2))
  let q := E.hom.left ≫ genericLeg S a k
  have hq : IsPullback q
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toSpec
      (stageScalarModel S a k).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k.val K))) :=
    overIso_modelStage_cartesian S a k _ E
  apply (IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) a).hom_ext
  · exact (curveModel_composite_triangle (simpleCurveCoefficientMap k.val G i)
      (projectiveStageIso S (ULift.{u} (Fin 2)) k).hom.left _ _ _
      (projectiveStageIso S (ULift.{u} (Fin 2)) k).hom.w
      (curveModel_projective_square k.val G i).w).trans hq.w.symm
  · have hl : (simpleCurveCoefficientMap k.val G i ≫
        (projectiveStageIso S (ULift.{u} (Fin 2)) k).hom.left) ≫ pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) a =
        simpleCurveCoefficientMap S G i :=
      projectiveCoefficient_triangle (Subalgebra.inclusion k.property.2).toRingHom
        (algebraMap k.val K) (algebraMap S K) rfl (simpleSchubertIso G i).hom.left
        (projectiveStageIso S (ULift.{u} (Fin 2)) k).hom.left _
        (projectiveBaseChange_snd (ULift.{u} (Fin 2))
          (Subalgebra.inclusion k.property.2).toRingHom)
        _ _ rfl rfl
    have hr : q ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) a =
        simpleCurveCoefficientMap S G i :=
      curveModel_composite_triangle E.hom.left (genericLeg S a k) _ _ _
        (genericLeg_projection S a k) h.flip.isoOverPullback_hom_left_comp_snd
    exact hl.trans hr.symm


/-- The two polynomial charts cover the projective line over any commutative ring. -/
theorem projectiveLine_polynomial_cover (R : Type u) [CommRing R]
    (x : projectiveScheme R (ULift.{u} (Fin 2))) :
    x ∈ Set.range (projectiveLinePolynomialChart R ⟨0⟩) ∨
      x ∈ Set.range (projectiveLinePolynomialChart R ⟨1⟩) := by
  obtain ⟨j, y, hy⟩ := Scheme.Cover.exists_eq
    (projectiveChartCover R (ULift.{u} (Fin 2))) x
  change ULift.{u} (Fin 2) at j
  let : IsOpenImmersion (projectiveLinePolynomialChart R j) :=
    projectiveLinePolynomialChart_open R j
  have hx : x ∈ (projectiveLinePolynomialChart R j).opensRange := by
    rw [projectiveLinePolynomialChart_range R j,
      ← projectiveChartMap_range R (ULift.{u} (Fin 2)) j]
    exact ⟨y, hy⟩
  rcases j with ⟨j⟩
  fin_cases j
  · exact Or.inl hx
  · exact Or.inr hx


end SchubertGeometry
