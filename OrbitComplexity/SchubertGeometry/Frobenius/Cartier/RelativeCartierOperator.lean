import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition
import OrbitComplexity.FrobeniusSplitting.Splittings.LaurentOperators
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorGluing
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorComparison
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorMorphisms

/-! # Cartier operators from the original projective-line section and a prior operator

Only the ground field is perfect. The coefficient ring may be nonperfect,
nonreduced, or zero. The two traces use the given prior coefficient operator.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting
noncomputable section
universe u v

namespace SchubertGeometry.ProjectiveCartier

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev indices := ULift.{u} (Fin 2)
private abbrev line (A : Type u) [CommRing A] := projectiveScheme A indices.{u}
private abbrev affine (A : Type u) [CommRing A] := Spec (.of (Polynomial A))
private abbrev overlap (A : Type u) [CommRing A] := Spec (.of (LaurentPolynomial A))
private abbrev chart (A : Type u) [CommRing A] (j : indices.{u}) :=
  projectiveLinePolynomialChart A j
private abbrev chartOpen (A : Type u) [CommRing A] (j : indices.{u}) :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule indices.{u} A) (MvPolynomial.X j)
private abbrev leftMap (A : Type u) [CommRing A] : overlap A ⟶ affine A :=
  Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial A →+* LaurentPolynomial A))
private abbrev rightMap (A : Type u) [CommRing A] : overlap A ⟶ affine A :=
  Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.invert.toRingHom.comp
      (Polynomial.toLaurent : Polynomial A →+* LaurentPolynomial A)))

private instance leftMap_open (A : Type u) [CommRing A] : IsOpenImmersion (leftMap A) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial A)

private theorem chart_cover (A : Type u) [CommRing A] :
    (⨆ j : indices.{u}, chartOpen A j) = ⊤ := by
  have h := (projectiveChartCover A indices.{u}).iSup_opensRange
  change (⨆ j : indices.{u}, (projectiveChartMap A indices.{u} j).opensRange) = ⊤ at h
  simpa only [projectiveChartMap_range] using h

variable {K : Type v} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

private abbrev sourceLine (A : Type u) [CommRing A] (p : ℕ) :=
  SchubertGeometry.ProjectiveLine.projectiveTransitionModule A (2 * (p - 1))

private def sectionWeight (s : (sourceLine A p).val.obj (op ⊤))
    (j : indices.{u}) : Polynomial A :=
  if j.down = 0 then
    (Scheme.ΓSpecIso (.of (Polynomial A))).hom
      (((pullback.fst (SchubertGeometry.ProjectiveLine.leftRestriction A)
        (SchubertGeometry.ProjectiveLine.twistedRestriction A (2 * (p - 1)))).val.app (op ⊤)).hom s)
  else
    (Scheme.ΓSpecIso (.of (Polynomial A))).hom
      (((pullback.snd (SchubertGeometry.ProjectiveLine.leftRestriction A)
        (SchubertGeometry.ProjectiveLine.twistedRestriction A (2 * (p - 1)))).val.app (op ⊤)).hom s)

private theorem specMap_top_value {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Γ(Spec (.of R), ⊤)) :
    (Scheme.ΓSpecIso (.of S)).hom ((Spec.map (CommRingCat.ofHom f)).appTop a) =
      f ((Scheme.ΓSpecIso (.of R)).hom a) :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)) a

private theorem specMap_comp_top_value {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (a : Γ(Spec (.of R), ⊤)) :
    (Scheme.ΓSpecIso (.of T)).hom
        ((Spec.map (CommRingCat.ofHom (g.comp f))).appTop a) =
      g (f ((Scheme.ΓSpecIso (.of R)).hom a)) :=
  specMap_top_value (g.comp f) a

private theorem pushforwardCongr_top {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : X.Modules) (a : Γ(M, ⊤)) :
    ((Scheme.Modules.pushforwardCongr h).hom.app M).app ⊤ a = a := by
  rw [Scheme.Modules.pushforwardCongr_hom_app_app]
  change M.presheaf.map (𝟙 (op ⊤)) a = a
  rw [CategoryTheory.Functor.map_id]
  rfl

private def unitRestrictionThrough {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (h : f ≫ g = k) :
    (Scheme.Modules.pushforward g).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward k).obj (SheafOfModules.unit X.ringCatSheaf) :=
  (Scheme.Modules.pushforward g).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp f g).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr h).hom.app _

private theorem modules_comp_value {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (a : Γ(M, ⊤)) :
    (f ≫ g).app ⊤ a = g.app ⊤ (f.app ⊤ a) := rfl

private theorem unitRestrictionThrough_top {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) (a : Γ(Y, ⊤)) :
    (unitRestrictionThrough f g k h).app ⊤ a = f.appTop a := by
  dsimp only [unitRestrictionThrough]
  erw [modules_comp_value, modules_comp_value, pushforwardCongr_top,
    Scheme.Modules.pushforwardComp_hom_app_app]
  rfl

private theorem leftRestriction_top_value
    (a : Γ(affine A, ⊤)) :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).hom
        (((SchubertGeometry.ProjectiveLine.leftRestriction A).val.app (op ⊤)).hom a) =
      Polynomial.toLaurent ((Scheme.ΓSpecIso (.of (Polynomial A))).hom a) := by
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).hom
    ((leftMap A).appTop a) = _
  exact specMap_top_value _ a

set_option maxHeartbeats 400000 in
private theorem rightRestriction_value (a : Γ(affine A, ⊤)) :
    (SchubertGeometry.ProjectiveLine.rightRestriction A).app ⊤ a = (rightMap A).appTop a := by
  let h : rightMap A ≫ chart A ⟨1⟩ = leftMap A ≫ chart A ⟨0⟩ :=
    (projectiveLinePolynomial_overlap A).symm
  have hv := unitRestrictionThrough_top (rightMap A) (chart A ⟨1⟩)
    (leftMap A ≫ chart A ⟨0⟩) h a
  change (SchubertGeometry.ProjectiveLine.rightRestriction A).app ⊤ a = (rightMap A).appTop a at hv
  exact hv

private theorem rightRestriction_top_value
    (a : Γ(affine A, ⊤)) :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).hom
        (((SchubertGeometry.ProjectiveLine.rightRestriction A).val.app (op ⊤)).hom a) =
      LaurentPolynomial.invert
        (Polynomial.toLaurent ((Scheme.ΓSpecIso (.of (Polynomial A))).hom a)) := by
  have hmap := specMap_comp_top_value
    (R := Polynomial A) (S := LaurentPolynomial A) (T := LaurentPolynomial A)
    (Polynomial.toLaurent : Polynomial A →+* LaurentPolynomial A)
    LaurentPolynomial.invert.toRingHom a
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).hom ((rightMap A).appTop a) =
    LaurentPolynomial.invert
      (Polynomial.toLaurent ((Scheme.ΓSpecIso (.of (Polynomial A))).hom a)) at hmap
  exact (congrArg (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).hom
    (rightRestriction_value (A := A) a)).trans hmap

private theorem twistedRestriction_top_value (d : ℕ)
    (a : Γ(affine A, ⊤)) :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).hom
        (((SchubertGeometry.ProjectiveLine.twistedRestriction A d).val.app (op ⊤)).hom a) =
      LaurentPolynomial.T (d : ℤ) * LaurentPolynomial.invert
        (Polynomial.toLaurent ((Scheme.ΓSpecIso (.of (Polynomial A))).hom a)) := by
  let b : Γ(overlap A, ⊤) :=
    (((SchubertGeometry.ProjectiveLine.rightRestriction A).val.app (op ⊤)).hom a)
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).hom
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial A))).inv
      (LaurentPolynomial.T (d : ℤ)) * b) = _
  rw [map_mul, Iso.inv_hom_id_apply]
  change LaurentPolynomial.T (d : ℤ) *
    (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).hom
      (((SchubertGeometry.ProjectiveLine.rightRestriction A).val.app (op ⊤)).hom a) = _
  rw [rightRestriction_top_value]

private theorem sectionWeight_matching (s : (sourceLine A p).val.obj (op ⊤)) :
    (sectionWeight s ⟨0⟩).toLaurent =
      LaurentPolynomial.T ((2 * (p - 1) : ℕ) : ℤ) *
        LaurentPolynomial.invert ((sectionWeight s ⟨1⟩).toLaurent) := by
  let a0 : Γ(affine A, ⊤) :=
    ((pullback.fst (SchubertGeometry.ProjectiveLine.leftRestriction A)
      (SchubertGeometry.ProjectiveLine.twistedRestriction A (2 * (p - 1)))).val.app (op ⊤)).hom s
  let a1 : Γ(affine A, ⊤) :=
    ((pullback.snd (SchubertGeometry.ProjectiveLine.leftRestriction A)
      (SchubertGeometry.ProjectiveLine.twistedRestriction A (2 * (p - 1)))).val.app (op ⊤)).hom s
  have hm : pullback.fst (SchubertGeometry.ProjectiveLine.leftRestriction A)
      (SchubertGeometry.ProjectiveLine.twistedRestriction A (2 * (p - 1))) ≫
        SchubertGeometry.ProjectiveLine.leftRestriction A =
    pullback.snd (SchubertGeometry.ProjectiveLine.leftRestriction A)
      (SchubertGeometry.ProjectiveLine.twistedRestriction A (2 * (p - 1))) ≫
        SchubertGeometry.ProjectiveLine.twistedRestriction A (2 * (p - 1)) := pullback.condition
  have h := congrArg
    (fun f : sourceLine A p ⟶ _ => f.app ⊤ s) hm
  change (SchubertGeometry.ProjectiveLine.leftRestriction A).app ⊤ a0 =
    (SchubertGeometry.ProjectiveLine.twistedRestriction A (2 * (p - 1))).app ⊤ a1 at h
  change Polynomial.toLaurent ((Scheme.ΓSpecIso (.of (Polynomial A))).hom a0) =
    LaurentPolynomial.T ((2 * (p - 1) : ℕ) : ℤ) * LaurentPolynomial.invert
      (Polynomial.toLaurent ((Scheme.ΓSpecIso (.of (Polynomial A))).hom a1))
  calc
    _ = (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).hom
        ((SchubertGeometry.ProjectiveLine.leftRestriction A).app ⊤ a0) :=
      (leftRestriction_top_value (A := A) a0).symm
    _ = (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).hom
        ((SchubertGeometry.ProjectiveLine.twistedRestriction A (2 * (p - 1))).app ⊤ a1) :=
      congrArg (Scheme.ΓSpecIso (.of (LaurentPolynomial A))).hom h
    _ = _ := twistedRestriction_top_value (A := A) (2 * (p - 1)) a1

private def localPolynomialOperator (ψ : FrobeniusLinearMap A p)
    (s : (sourceLine A p).val.obj (op ⊤)) (j : indices.{u}) :
    FrobeniusLinearMap (Polynomial A) p :=
  (polynomialTraceOfOperator (K := K) ψ).weight (sectionWeight s j)

private def overlapOperator (ψ : FrobeniusLinearMap A p)
    (s : (sourceLine A p).val.obj (op ⊤)) :
    FrobeniusLinearMap (LaurentPolynomial A) p :=
  (laurentTraceOfOperator (K := K) ψ).weight (sectionWeight s ⟨0⟩).toLaurent

private theorem leftOperator_ring (ψ : FrobeniusLinearMap A p)
    (s : (sourceLine A p).val.obj (op ⊤)) (f : Polynomial A) :
    overlapOperator (K := K) ψ s f.toLaurent =
      (localPolynomialOperator (K := K) ψ s ⟨0⟩ f).toLaurent := by
  change laurentTraceOfOperator (K := K) ψ
    ((sectionWeight s ⟨0⟩).toLaurent * f.toLaurent) = _
  rw [← map_mul, laurentOperator_toLaurent]
  rfl

private theorem rightOperator_ring (ψ : FrobeniusLinearMap A p)
    (s : (sourceLine A p).val.obj (op ⊤)) (f : Polynomial A) :
    overlapOperator (K := K) ψ s (LaurentPolynomial.invert f.toLaurent) =
      LaurentPolynomial.invert (localPolynomialOperator (K := K) ψ s ⟨1⟩ f).toLaurent := by
  change laurentTraceOfOperator (K := K) ψ
    ((sectionWeight s ⟨0⟩).toLaurent * LaurentPolynomial.invert f.toLaurent) =
      LaurentPolynomial.invert
        (polynomialTraceOfOperator (K := K) ψ (sectionWeight s ⟨1⟩ * f)).toLaurent
  rw [sectionWeight_matching]
  have hc : ((2 * (p - 1) : ℕ) : ℤ) = 2 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
      (ne_of_gt (expChar_pos K p))), Nat.cast_one]
  have he := laurentOperator_invert (K := K) ψ
    ((sectionWeight s ⟨1⟩ * f).toLaurent)
  rw [laurentOperator_toLaurent, ← hc] at he
  simpa only [map_mul, mul_assoc] using he

private def localOperator (ψ : FrobeniusLinearMap A p)
    (s : (sourceLine A p).val.obj (op ⊤)) (j : indices.{u}) :
    SchemeFrobeniusMap (chartOpen A j).toScheme p :=
  ((localPolynomialOperator (K := K) ψ s j).toSpec (expChar_pos K p)).pushforward
    (projectiveLinePolynomialIso A j).hom

private theorem polynomialCharts_overlap (hp : 0 < p)
    (P0 P1 : FrobeniusLinearMap (Polynomial A) p)
    (L : FrobeniusLinearMap (LaurentPolynomial A) p)
    (hL : ∀ f : Polynomial A, L f.toLaurent = (P0 f).toLaurent)
    (hR : ∀ f : Polynomial A, L (LaurentPolynomial.invert f.toLaurent) =
      LaurentPolynomial.invert (P1 f).toLaurent)
    (V : (line A).Opens) (h0 : V ≤ chartOpen A ⟨0⟩) (h1 : V ≤ chartOpen A ⟨1⟩) :
    ((P0.toSpec hp).pushforward (projectiveLinePolynomialIso A ⟨0⟩).hom).onSubopen V h0 =
      ((P1.toSpec hp).pushforward (projectiveLinePolynomialIso A ⟨1⟩).hom).onSubopen V h1 := by
  apply SchemeFrobeniusMap.chartFormula_eq
    (chartOpen A ⟨0⟩) (chartOpen A ⟨1⟩)
    (projectiveLinePolynomialIso A ⟨0⟩) (projectiveLinePolynomialIso A ⟨1⟩)
    (P0.toSpec hp) (P1.toSpec hp) (L.toSpec hp) (leftMap A) (rightMap A)
  · exact FrobeniusLinearMap.toSpec_naturality P0 L hp Polynomial.toLaurent hL
  · exact FrobeniusLinearMap.toSpec_naturality P1 L hp
      (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) hR
  · exact projectiveLinePolynomial_overlap A
  · change V ≤ (leftMap A ≫ chart A ⟨0⟩).opensRange
    rw [projectiveLinePolynomial_inter]
    exact le_inf h0 h1

private theorem localOperator_overlap (ψ : FrobeniusLinearMap A p)
    (s : (sourceLine A p).val.obj (op ⊤)) (V : (line A).Opens)
    (h0 : V ≤ chartOpen A ⟨0⟩) (h1 : V ≤ chartOpen A ⟨1⟩) :
    (localOperator (K := K) ψ s ⟨0⟩).onSubopen V h0 =
      (localOperator (K := K) ψ s ⟨1⟩).onSubopen V h1 := by
  exact polynomialCharts_overlap (expChar_pos K p)
    (localPolynomialOperator (K := K) ψ s ⟨0⟩)
    (localPolynomialOperator (K := K) ψ s ⟨1⟩) (overlapOperator (K := K) ψ s)
    (leftOperator_ring (K := K) ψ s) (rightOperator_ring (K := K) ψ s) V h0 h1

private theorem localOperator_compatible (ψ : FrobeniusLinearMap A p)
    (s : (sourceLine A p).val.obj (op ⊤))
    (i j : indices.{u}) (V : (line A).Opens)
    (hi : V ≤ chartOpen A i) (hj : V ≤ chartOpen A j) :
    (localOperator (K := K) ψ s i).onSubopen V hi =
      (localOperator (K := K) ψ s j).onSubopen V hj := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j
  · rfl
  · exact localOperator_overlap (K := K) ψ s V hi hj
  · exact (localOperator_overlap (K := K) ψ s V hj hi).symm
  · rfl

/-- The prior coefficient operator and the original line section construct a global
operator, without a perfectness assumption on the chart ring. -/
def relativeCartierOperator (ψ : FrobeniusLinearMap A p)
    (s : (sourceLine A p).val.obj (op ⊤)) : SchemeFrobeniusMap (line A) p :=
  SchemeFrobeniusMap.glue (chartOpen A) (localOperator (K := K) ψ s)
    (localOperator_compatible (K := K) ψ s) (chart_cover A)

/-- On both original polynomial charts, the operator is the prior trace weighted by
the original section's raw projection. -/
theorem relativeCartierOperator_chart (ψ : FrobeniusLinearMap A p)
    (s : (sourceLine A p).val.obj (op ⊤)) (j : indices.{u}) :
    (relativeCartierOperator (K := K) ψ s).restrict (chartOpen A j) =
      (((polynomialTraceOfOperator (K := K) ψ).weight (sectionWeight s j)).toSpec
        (expChar_pos K p)).pushforward (projectiveLinePolynomialIso A j).hom :=
  SchemeFrobeniusMap.glue_restrict _ _ _ _ j

end SchubertGeometry.ProjectiveCartier
