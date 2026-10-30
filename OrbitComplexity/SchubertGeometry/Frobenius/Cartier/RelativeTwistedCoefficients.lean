import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierComparison
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections
import OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveOperators
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coefficients of the relative Cartier splitting section -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting
noncomputable section
universe u v w

namespace SchubertGeometry.ProjectiveCartier

open private line sourceLine unitLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

open private insertedInfinity
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections

open private rawLeft rawRight
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierComparison

open private structureModule chartModule chartSection chartSection_top
  endpointLeft endpointRight endpointLift endpoint_matching endpoint_hasPullback
  matchingPullbackLift module_comp_apply
  from OrbitComplexity.SchubertGeometry.LineBundles.Affine.GlobalAffineEndpoint

open private infinity_fst infinity_snd chart1Multiply polynomialPower
  from OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.InfinityFactor

private def splittingFrame (A : Type u) [CommRing A] (p : ℕ) :
    structureModule (line A) ⟶ ProjectiveLine.projectiveTransitionModule A (p - 1) :=
  ProjectiveLine.projectiveAffineEndpoint A (p - 1) 1 0

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: matchingPullbackLift_fst"

private theorem matchingPullbackLift_fst {D : Type v} [Category.{w} D]
    {W X Y Z : D} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (hm : h ≫ f = k ≫ g) :
    matchingPullbackLift f g h k hm ≫ pullback.fst f g = h := by
  change pullback.lift h k hm ≫ pullback.fst f g = h
  exact pullback.lift_fst h k hm

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: matchingPullbackLift_snd"

private theorem matchingPullbackLift_snd {D : Type v} [Category.{w} D]
    {W X Y Z : D} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (hm : h ≫ f = k ≫ g) :
    matchingPullbackLift f g h k hm ≫ pullback.snd f g = k := by
  change pullback.lift h k hm ≫ pullback.snd f g = k
  exact pullback.lift_snd h k hm

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: endpoint_fst"

private theorem endpoint_fst (A : Type u) [CommRing A] (d : ℕ) (c b : A) :
    ProjectiveLine.projectiveAffineEndpoint A d c b ≫
        pullback.fst (ProjectiveLine.leftRestriction A)
          (ProjectiveLine.twistedRestriction A d) = endpointLeft A d c b := by
  let : HasPullback (ProjectiveLine.leftRestriction A)
      (ProjectiveLine.twistedRestriction A d) := endpoint_hasPullback A d
  exact matchingPullbackLift_fst (D := (line A).Modules)
    (W := structureModule (line A)) (ProjectiveLine.leftRestriction A)
    (ProjectiveLine.twistedRestriction A d) (endpointLeft A d c b)
    (endpointRight A d c b) (endpoint_matching A d c b)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: endpoint_snd"

private theorem endpoint_snd (A : Type u) [CommRing A] (d : ℕ) (c b : A) :
    ProjectiveLine.projectiveAffineEndpoint A d c b ≫
        pullback.snd (ProjectiveLine.leftRestriction A)
          (ProjectiveLine.twistedRestriction A d) = endpointRight A d c b := by
  let : HasPullback (ProjectiveLine.leftRestriction A)
      (ProjectiveLine.twistedRestriction A d) := endpoint_hasPullback A d
  exact matchingPullbackLift_snd (D := (line A).Modules)
    (W := structureModule (line A)) (ProjectiveLine.leftRestriction A)
    (ProjectiveLine.twistedRestriction A d) (endpointLeft A d c b)
    (endpointRight A d c b) (endpoint_matching A d c b)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: module_comp_app"

private theorem module_comp_app {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (U : X.Opens) (a : Γ(M, U)) :
    ((f ≫ g).app U).hom a = (g.app U).hom ((f.app U).hom a) := rfl

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: append_projection"

private theorem append_projection {D : Type v} [Category.{w} D]
    {W X Y Z : D} (m : W ⟶ X) (f : X ⟶ Y) (π : Y ⟶ Z) (g : X ⟶ Z)
    (h : f ≫ π = g) : (m ≫ f) ≫ π = m ≫ g :=
  (Category.assoc m f π).trans (congrArg (fun k : X ⟶ Z => m ≫ k) h)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: unitSmul_top"

private theorem unitSmul_top {X : Scheme.{u}} (r a : Γ(X, ⊤)) :
    ((Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r).app ⊤).hom a =
      r * a := by
  have hs :
      ((Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r).app ⊤).hom a =
        X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op r * a :=
    ConcreteCategory.congr_hom
      (Scheme.Modules.globalSectionsSmul_app (SheafOfModules.unit X.ringCatSheaf) r ⊤) a
  have hr : X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op r = r := by
    change X.presheaf.map (𝟙 (op ⊤)) r = r
    have hid : X.presheaf.map (𝟙 (op ⊤)) = 𝟙 (X.presheaf.obj (op ⊤)) :=
      X.presheaf.map_id (op ⊤)
    exact ConcreteCategory.congr_hom hid r
  exact hs.trans (congrArg (fun b : Γ(X, ⊤) => b * a) hr)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: pushedUnitSmul_top"

private theorem pushedUnitSmul_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r a : Γ(X, ⊤)) :
    ((((Scheme.Modules.pushforward f).map
      (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r)).app ⊤).hom a) =
      r * a :=
  unitSmul_top r a

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: chart1Multiply_top"

private theorem chart1Multiply_top (A : Type u) [CommRing A] (d : ℕ)
    (a : Γ(Spec (.of (Polynomial A)), ⊤)) :
    ((chart1Multiply A d).app ⊤).hom a =
      (Scheme.ΓSpecIso (.of (Polynomial A))).inv (Polynomial.X ^ d) * a :=
  pushedUnitSmul_top (projectiveLinePolynomialChart A ⟨1⟩)
    ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (Polynomial.X ^ d)) a

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: endpointLeft_top"

private theorem endpointLeft_top (A : Type u) [CommRing A] (d : ℕ) (c b : A) :
    ((endpointLeft A d c b).app ⊤).hom (1 : Γ(line A, ⊤)) =
      (Scheme.ΓSpecIso (.of (Polynomial A))).inv
        ((Polynomial.C c * Polynomial.X + Polynomial.C b) ^ d) :=
  chartSection_top A ⟨0⟩ ((Polynomial.C c * Polynomial.X + Polynomial.C b) ^ d)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: endpointRight_top"

private theorem endpointRight_top (A : Type u) [CommRing A] (d : ℕ) (c b : A) :
    ((endpointRight A d c b).app ⊤).hom (1 : Γ(line A, ⊤)) =
      (Scheme.ΓSpecIso (.of (Polynomial A))).inv
        ((Polynomial.C c + Polynomial.C b * Polynomial.X) ^ d) :=
  chartSection_top A ⟨1⟩ ((Polynomial.C c + Polynomial.C b * Polynomial.X) ^ d)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: endpointLeft_one"

private theorem endpointLeft_one (A : Type u) [CommRing A] (d : ℕ) :
    ((endpointLeft A d 1 0).app ⊤).hom (1 : Γ(line A, ⊤)) =
      (Scheme.ΓSpecIso (.of (Polynomial A))).inv (Polynomial.X ^ d) := by
  have hpoly : (Polynomial.C (1 : A) * Polynomial.X + Polynomial.C (0 : A)) ^ d =
      Polynomial.X ^ d := by
    rw [Polynomial.C_1, Polynomial.C_0, one_mul, add_zero]
  exact (endpointLeft_top A d 1 0).trans
    (congrArg (Scheme.ΓSpecIso (.of (Polynomial A))).inv hpoly)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: endpointRight_one"

private theorem endpointRight_one (A : Type u) [CommRing A] (d : ℕ) :
    ((endpointRight A d 1 0).app ⊤).hom (1 : Γ(line A, ⊤)) =
      (1 : Γ(Spec (.of (Polynomial A)), ⊤)) := by
  have hpoly : (Polynomial.C (1 : A) + Polynomial.C (0 : A) * Polynomial.X) ^ d =
      (1 : Polynomial A) := by
    rw [Polynomial.C_1, Polynomial.C_0, zero_mul, add_zero, one_pow]
  have hone : (Scheme.ΓSpecIso (.of (Polynomial A))).inv (1 : Polynomial A) =
      (1 : Γ(Spec (.of (Polynomial A)), ⊤)) :=
    (Scheme.ΓSpecIso (.of (Polynomial A))).inv.hom.map_one
  exact (endpointRight_top A d 1 0).trans
    ((congrArg (fun a : Polynomial A => (Scheme.ΓSpecIso (.of (Polynomial A))).inv a)
      hpoly).trans hone)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: splittingFrame_left"

private theorem splittingFrame_left (A : Type u) [CommRing A] (p : ℕ) :
    rawLeft (p := p) (insertedInfinity (p := p) (splittingFrame A p)) = Polynomial.X ^ (p - 1) := by
  let m : structureModule (line A) ⟶ ProjectiveLine.projectiveTransitionModule A (p - 1) :=
    splittingFrame A p
  let f := ProjectiveLine.projectiveInfinityFactor A (p - 1)
  let π := pullback.fst (ProjectiveLine.leftRestriction A)
    (ProjectiveLine.twistedRestriction A (2 * (p - 1)))
  let σ := pullback.fst (ProjectiveLine.leftRestriction A)
    (ProjectiveLine.twistedRestriction A (p - 1))
  have hi : (m ≫ f) ≫ π = m ≫ σ := append_projection m f π σ (infinity_fst A (p - 1))
  have he : m ≫ σ = endpointLeft A (p - 1) 1 0 := endpoint_fst A (p - 1) 1 0
  have hproj : (m ≫ f) ≫ π = endpointLeft A (p - 1) 1 0 := hi.trans he
  have hv := congrArg
    (fun q : structureModule (line A) ⟶ chartModule A ⟨0⟩ =>
      (q.app ⊤).hom (1 : Γ(line A, ⊤))) hproj
  have hcomp := module_comp_app (m ≫ f) π ⊤ (1 : Γ(line A, ⊤))
  have hvalue := hcomp.symm.trans (hv.trans (endpointLeft_one A (p - 1)))
  exact (congrArg (Scheme.ΓSpecIso (.of (Polynomial A))).hom hvalue).trans
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (Polynomial A))).inv_hom_id
      (Polynomial.X ^ (p - 1)))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: splittingFrame_right"

private theorem splittingFrame_right (A : Type u) [CommRing A] (p : ℕ) :
    rawRight (p := p) (insertedInfinity (p := p) (splittingFrame A p)) = Polynomial.X ^ (p - 1) :=
      by
  let m : structureModule (line A) ⟶ ProjectiveLine.projectiveTransitionModule A (p - 1) :=
    splittingFrame A p
  let f := ProjectiveLine.projectiveInfinityFactor A (p - 1)
  let π := pullback.snd (ProjectiveLine.leftRestriction A)
    (ProjectiveLine.twistedRestriction A (2 * (p - 1)))
  let σ := pullback.snd (ProjectiveLine.leftRestriction A)
    (ProjectiveLine.twistedRestriction A (p - 1))
  let t := chart1Multiply A (p - 1)
  have hi : (m ≫ f) ≫ π = m ≫ (σ ≫ t) :=
    append_projection m f π (σ ≫ t) (infinity_snd A (p - 1))
  have he : m ≫ σ = endpointRight A (p - 1) 1 0 := endpoint_snd A (p - 1) 1 0
  have hp : (m ≫ σ) ≫ t = endpointRight A (p - 1) 1 0 ≫ t :=
    congrArg (fun q : structureModule (line A) ⟶ chartModule A ⟨1⟩ => q ≫ t) he
  have hproj : (m ≫ f) ≫ π = endpointRight A (p - 1) 1 0 ≫ t :=
    hi.trans ((Category.assoc m σ t).symm.trans hp)
  have hv := congrArg
    (fun q : structureModule (line A) ⟶ chartModule A ⟨1⟩ =>
      (q.app ⊤).hom (1 : Γ(line A, ⊤))) hproj
  have hcomp := module_comp_app (m ≫ f) π ⊤ (1 : Γ(line A, ⊤))
  have hright := module_comp_app (endpointRight A (p - 1) 1 0) t ⊤ (1 : Γ(line A, ⊤))
  have hinput := congrArg
    (fun a : Γ(Spec (.of (Polynomial A)), ⊤) => (t.app ⊤).hom a)
    (endpointRight_one A (p - 1))
  have houtput : (t.app ⊤).hom (1 : Γ(Spec (.of (Polynomial A)), ⊤)) =
      (Scheme.ΓSpecIso (.of (Polynomial A))).inv (Polynomial.X ^ (p - 1)) :=
    (chart1Multiply_top A (p - 1) (1 : Γ(Spec (.of (Polynomial A)), ⊤))).trans
      (mul_one ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (Polynomial.X ^ (p - 1)) :
        Γ(Spec (.of (Polynomial A)), ⊤)))
  have hvalue := hcomp.symm.trans (hv.trans (hright.trans (hinput.trans houtput)))
  exact (congrArg (Scheme.ΓSpecIso (.of (Polynomial A))).hom hvalue).trans
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (Polynomial A))).inv_hom_id
      (Polynomial.X ^ (p - 1)))

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A] [ExpChar A p]

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: splittingOperator_eq"

private theorem splittingOperator_eq (base : RingSplitting A p) :
    relativeCartierOperator (K := K) base.toOperator
        (insertedInfinity (p := p) (splittingFrame A p)) =
      (projectiveLineSplitting base).toOperator := by
  have h0 : rawLeft (p := p) (insertedInfinity (p := p) (splittingFrame A p)) =
      Polynomial.C ((Nat.choose (p - 1) (0 : ℕ) : ℕ) : A) *
        Polynomial.X ^ (p - 1 - (0 : ℕ)) := by
    simpa only [Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one,
      Polynomial.C_1, one_mul] using splittingFrame_left A p
  have h1 : rawRight (p := p) (insertedInfinity (p := p) (splittingFrame A p)) =
      Polynomial.C ((Nat.choose (p - 1) (0 : ℕ) : ℕ) : A) *
        Polynomial.X ^ (p - 1 + (0 : ℕ)) := by
    simpa only [Nat.choose_zero_right, Nat.add_zero, Nat.cast_one,
      Polynomial.C_1, one_mul] using splittingFrame_right A p
  exact (relativeCartierOperator_eq_coefficient (K := K) base.toOperator
    (insertedInfinity (p := p) (splittingFrame A p)) ⟨0, expChar_pos A p⟩ h0 h1).trans
    ((projectiveLineCoeffOperator_normalized (K := K) base ⟨0, expChar_pos A p⟩).trans
      (projectiveLineCanonicalOperator_zero base))


end SchubertGeometry.ProjectiveCartier
