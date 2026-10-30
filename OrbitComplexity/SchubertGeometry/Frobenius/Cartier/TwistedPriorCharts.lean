import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorOperator
import OrbitComplexity.SchubertGeometry.Normality.Transitions.RetainedPriorCharts
import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialOperators
import OrbitComplexity.FrobeniusSplitting.Cartier.SectionTransport

/-! # Twisted prior operators on the retained affine charts

One line-valued Frobenius map supplies every coefficient operator. The original
cocone arrows and the inverse-character frame rule give their restriction law.
No determinant section is inserted into these coefficient operators.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting
noncomputable section
universe u v w

namespace SchubertGeometry.ProjectiveCartier

private abbrev coordinateSpec {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) := Spec.map (CommRingCat.ofHom f)

private def chartCoordinateIso {Y : Scheme.{u}} {A : Type u} [CommRing A]
    (j : Spec (.of A) ⟶ Y) [IsOpenImmersion j] :
    Γ(Y, j.opensRange) ≅ CommRingCat.of A :=
  j.opensRange.topIso.symm ≪≫
    Scheme.Γ.mapIso j.isoOpensRange.op ≪≫ Scheme.ΓSpecIso (.of A)

@[nolint unusedArguments]
private theorem chartRange_le {Y : Scheme.{u}} {A B : Type u}
    [CommRing A] [CommRing B] (j : Spec (.of A) ⟶ Y) (k : Spec (.of B) ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k] (f : A →+* B)
    [IsOpenImmersion (coordinateSpec f)] (h : coordinateSpec f ≫ j = k) :
    k.opensRange ≤ j.opensRange := by
  intro y hy
  obtain ⟨x, rfl⟩ := Scheme.Hom.mem_opensRange.mp hy
  refine Scheme.Hom.mem_opensRange.mpr ⟨(coordinateSpec f) x, ?_⟩
  exact congrArg (fun q : Spec (.of B) ⟶ Y => q x) h

private theorem chartCoordinateIso_natural {Y : Scheme.{u}} {A B : Type u}
    [CommRing A] [CommRing B] (j : Spec (.of A) ⟶ Y) (k : Spec (.of B) ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k] (f : A →+* B)
    [IsOpenImmersion (coordinateSpec f)] (h : coordinateSpec f ≫ j = k) :
    Y.presheaf.map (homOfLE (chartRange_le j k f h)).op ≫ (chartCoordinateIso k).hom =
      (chartCoordinateIso j).hom ≫ CommRingCat.ofHom f := by
  let hle : k.opensRange ≤ j.opensRange := chartRange_le j k f h
  have hsquare : coordinateSpec f ≫ j.isoOpensRange.hom =
      k.isoOpensRange.hom ≫ Y.homOfLE hle := by
    apply (cancel_mono j.opensRange.ι).1
    simpa only [Category.assoc, Scheme.homOfLE_ι,
      Scheme.Hom.isoOpensRange_hom_ι] using h
  have hΓ := congrArg
    (fun m : Spec (.of B) ⟶ j.opensRange.toScheme => m.appTop) hsquare
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hΓ
  ext a
  change (Scheme.ΓSpecIso (.of B)).hom
      (k.isoOpensRange.hom.appTop
        (k.opensRange.topIso.inv (Y.presheaf.map (homOfLE hle).op a))) =
    f ((Scheme.ΓSpecIso (.of A)).hom
      (j.isoOpensRange.hom.appTop (j.opensRange.topIso.inv a)))
  have htop := FrobeniusSplitting.OperatorSheaf.homOfLE_topIso_inv hle a
  have hpoint := ConcreteCategory.congr_hom hΓ (j.opensRange.topIso.inv a)
  calc
    _ = (Scheme.ΓSpecIso (.of B)).hom
        (k.isoOpensRange.hom.appTop
          ((Y.homOfLE hle).appTop (j.opensRange.topIso.inv a))) :=
      congrArg (fun z => (Scheme.ΓSpecIso (.of B)).hom
        (k.isoOpensRange.hom.appTop z)) htop.symm
    _ = (Scheme.ΓSpecIso (.of B)).hom
        ((coordinateSpec f).appTop
          (j.isoOpensRange.hom.appTop (j.opensRange.topIso.inv a))) :=
      congrArg (fun z => (Scheme.ΓSpecIso (.of B)).hom z) hpoint.symm
    _ = _ := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
      (j.isoOpensRange.hom.appTop (j.opensRange.topIso.inv a))

variable {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]

private def chartTwistedOperator {Y : Scheme.{u}} {A : Type u} [CommRing A]
    (base : Y ⟶ Spec (.of C)) (L : Y.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (j : Spec (.of A) ⟶ Y) [IsOpenImmersion j] (e : Γ(L, j.opensRange)) :
    FrobeniusLinearMap A p :=
  (twistedFrameOperator base L Θ j.opensRange e).transport
    (chartCoordinateIso j).commRingCatIsoToRingEquiv

private theorem chartTwistedOperator_natural {Y : Scheme.{u}} {A B : Type u}
    [CommRing A] [CommRing B] (base : Y ⟶ Spec (.of C)) (L : Y.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (j : Spec (.of A) ⟶ Y) (k : Spec (.of B) ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k] (f : A →+* B)
    [IsOpenImmersion (coordinateSpec f)] (h : coordinateSpec f ≫ j = k)
    (e : Γ(L, j.opensRange)) (e' : Γ(L, k.opensRange)) (g : Γ(Y, k.opensRange))
    (he : L.presheaf.map (homOfLE (chartRange_le j k f h)).op e = g • e') (a : A) :
    chartTwistedOperator base L Θ k e' ((chartCoordinateIso k).hom g * f a) =
      f (chartTwistedOperator base L Θ j e a) := by
  let hle : k.opensRange ≤ j.opensRange := chartRange_le j k f h
  let r := Y.presheaf.map (homOfLE hle).op
  let α := (chartCoordinateIso j).commRingCatIsoToRingEquiv
  let β := (chartCoordinateIso k).commRingCatIsoToRingEquiv
  have hd : ∀ b : Γ(Y, j.opensRange), β (r b) = f (α b) := by
    intro b
    exact ConcreteCategory.congr_hom (chartCoordinateIso_natural j k f h) b
  have hi : β.symm (β g * f a) = g * r (α.symm a) := by
    apply β.injective
    rw [RingEquiv.apply_symm_apply, map_mul, hd, RingEquiv.apply_symm_apply]
  change β (twistedFrameOperator base L Θ k.opensRange e'
      (β.symm (β g * f a))) =
    f (α (twistedFrameOperator base L Θ j.opensRange e (α.symm a)))
  rw [hi, twistedFrameOperator_restrict base L Θ hle e e' g he]
  exact hd (twistedFrameOperator base L Θ j.opensRange e (α.symm a))

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{w} J] [Quiver.IsThin J] [Small.{u} J]
variable (N : J ⥤ CommAlgCat.{u} R)
variable [∀ {s t} (f : s ⟶ t), IsOpenImmersion
  (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
variable [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
  Scheme.forget).IsLocallyDirected]
variable (cG : Cocone (N.op ⋙ algSpec (.of R))) (hcG : IsColimit cG)

private def retainedChartRange (s : J) : cG.pt.left.Opens := by
  let : IsOpenImmersion (cG.ι.app (op s)).left :=
    (retained_prior_charts N cG hcG).1 s
  exact (cG.ι.app (op s)).left.opensRange

private def retainedCoordinateIso (s : J) :
    Γ(cG.pt.left, retainedChartRange N cG hcG s) ≅ CommRingCat.of (N.obj s) := by
  let hj : IsOpenImmersion (cG.ι.app (op s)).left :=
    (retained_prior_charts N cG hcG).1 s
  exact @chartCoordinateIso cG.pt.left (N.obj s) _ (cG.ι.app (op s)).left hj

/-- The original retained ring receives its coefficient operator from the
line-valued prior map in that chart's unit frame. -/
def retainedTwistedPriorOperator
    (base : cG.pt.left ⟶ Spec (.of C)) (L : cG.pt.left.Modules)
    (Θ : frobeniusRestriction C p base L ⟶
      SheafOfModules.unit cG.pt.left.ringCatSheaf) (s : J)
    (e : Γ(L, retainedChartRange N cG hcG s)) :
    FrobeniusLinearMap (N.obj s) p := by
  let hj : IsOpenImmersion (cG.ι.app (op s)).left :=
    (retained_prior_charts N cG hcG).1 s
  exact @chartTwistedOperator C _ p _ cG.pt.left (N.obj s) _
    base L Θ (cG.ι.app (op s)).left hj e

/-- The inverse-character unit-frame rule determines the original coefficient
restriction, rather than imposing compatibility on independently chosen maps. -/
theorem retainedTwistedPriorOperator_map
    (base : cG.pt.left ⟶ Spec (.of C)) (L : cG.pt.left.Modules)
    (Θ : frobeniusRestriction C p base L ⟶
      SheafOfModules.unit cG.pt.left.ringCatSheaf) {s t : J} (f : s ⟶ t)
    (e : Γ(L, retainedChartRange N cG hcG s))
    (e' : Γ(L, retainedChartRange N cG hcG t))
    (g : Γ(cG.pt.left, retainedChartRange N cG hcG t))
    (hle : retainedChartRange N cG hcG t ≤ retainedChartRange N cG hcG s)
    (he : L.presheaf.map (homOfLE hle).op e = g • e') (a : N.obj s) :
    retainedTwistedPriorOperator N cG hcG base L Θ t e'
        ((retainedCoordinateIso N cG hcG t).hom g * (N.map f).hom a) =
      (N.map f).hom (retainedTwistedPriorOperator N cG hcG base L Θ s e a) := by
  let hs : IsOpenImmersion (cG.ι.app (op s)).left :=
    (retained_prior_charts N cG hcG).1 s
  let ht : IsOpenImmersion (cG.ι.app (op t)).left :=
    (retained_prior_charts N cG hcG).1 t
  exact @chartTwistedOperator_natural C _ p _ cG.pt.left (N.obj s) (N.obj t) _ _
    base L Θ (cG.ι.app (op s)).left (cG.ι.app (op t)).left hs ht
    (N.map f).hom.toRingHom inferInstance
    ((retained_prior_charts N cG hcG).2.1 s t f) e e' g he a

variable {K : Type u} [Field K] [ExpChar K p] [PerfectRing K p]

/-- Polynomial fibre traces inherit the same full-character input factor on the
retained prior overlap. No determinant coefficient is inserted at this stage. -/
theorem retainedTwistedPriorTrace_map [Algebra K R]
    (base : cG.pt.left ⟶ Spec (.of K)) (L : cG.pt.left.Modules)
    (Θ : frobeniusRestriction K p base L ⟶
      SheafOfModules.unit cG.pt.left.ringCatSheaf)
    {s t : J} (f : s ⟶ t)
    (e : Γ(L, retainedChartRange N cG hcG s))
    (e' : Γ(L, retainedChartRange N cG hcG t))
    (g : Γ(cG.pt.left, retainedChartRange N cG hcG t))
    (hle : retainedChartRange N cG hcG t ≤ retainedChartRange N cG hcG s)
    (he : L.presheaf.map (homOfLE hle).op e = g • e') (Q : Polynomial (N.obj s)) :
    letI : Algebra K (N.obj s) :=
      ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
    letI : Algebra K (N.obj t) :=
      ((algebraMap R (N.obj t)).comp (algebraMap K R)).toAlgebra
    let g' := (retainedCoordinateIso N cG hcG t).hom g
    polynomialTraceOfOperator (K := K)
        (retainedTwistedPriorOperator N cG hcG base L Θ t e')
        (Polynomial.C g' * Polynomial.map (N.map f).hom.toRingHom Q) =
      Polynomial.map (N.map f).hom.toRingHom
        (polynomialTraceOfOperator (K := K)
          (retainedTwistedPriorOperator N cG hcG base L Θ s e) Q) := by
  let : Algebra K (N.obj s) :=
    ((algebraMap R (N.obj s)).comp (algebraMap K R)).toAlgebra
  let : Algebra K (N.obj t) :=
    ((algebraMap R (N.obj t)).comp (algebraMap K R)).toAlgebra
  apply Polynomial.ext
  intro n
  simp only [polynomialTraceOfOperator_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_map]
  exact retainedTwistedPriorOperator_map N cG hcG base L Θ f e e' g hle he
    (Q.coeff (p * n + (p - 1)))

end SchubertGeometry.ProjectiveCartier
