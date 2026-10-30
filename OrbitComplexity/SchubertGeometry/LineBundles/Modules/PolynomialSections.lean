import OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalCoordinates
import TauCeti.AlgebraicGeometry.Modules.GlobalSections
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Global sections from polynomials of bounded degree -/

open AlgebraicGeometry CategoryTheory Opposite GroupActions
open AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
noncomputable section
universe u v w
namespace SchubertGeometry.ProjectiveLine

open private line affine chart structureModule
  from OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalMonomials

private theorem restrictAdditive {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : (restrictFunctor f).Additive where
  map_add := by intros; rfl

private theorem restrict_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (r : Γ(Y, ⊤)) :
    (restrictFunctor f).map (globalSectionsSmul M r) =
      globalSectionsSmul ((restrictFunctor f).obj M) (f.appTop r) := by
  let eta := restrictFunctorIsoPullback f
  let _ : IsIso (eta.hom.app M) := (eta.app M).isIso_hom
  apply (cancel_mono (eta.hom.app M)).mp
  exact (eta.hom.naturality (globalSectionsSmul M r)).trans
    ((congrArg (fun e => eta.hom.app M ≫ e)
      (pullback_map_globalSectionsSmul f M r)).trans
        (globalSectionsSmul_naturality (eta.hom.app M) (f.appTop r)).symm)

private theorem restrict_scalar_frame {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (N : X.Modules)
    (e : (restrictFunctor f).obj M ⟶ N) (a : Γ(Y, ⊤)) :
    (restrictFunctor f).map (globalSectionsSmul M a) ≫ e =
      e ≫ globalSectionsSmul N (f.appTop a) :=
  (congrArg (fun z => z ≫ e) (restrict_scalar f M a)).trans
    (globalSectionsSmul_naturality e (f.appTop a))

private theorem restrict_unit_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (a : Γ(Y, ⊤)) :
    (restrictFunctor f).map (globalSectionsSmul (SheafOfModules.unit Y.ringCatSheaf) a) ≫
        (restrictUnitIso f).hom =
      (restrictUnitIso f).hom ≫
        globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) (f.appTop a) :=
  restrict_scalar_frame f _ _ (restrictUnitIso f).hom a

private theorem source_weighted_functor {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {S M : C} {N : D} (eta : F.obj S ⟶ N) (e : F.obj M ⟶ N)
    (m : S ⟶ M) (r : S ⟶ S) (t : M ⟶ M) (u v w : N ⟶ N)
    (hm : F.map m ≫ e = eta ≫ v) (hn : r ≫ m = m ≫ t)
    (hr : F.map r ≫ eta = eta ≫ u) (hs : u ≫ v = w) :
    F.map (m ≫ t) ≫ e = eta ≫ w := by
  calc
    F.map (m ≫ t) ≫ e = F.map (r ≫ m) ≫ e := congrArg (fun z => F.map z ≫ e) hn.symm
    _ = (F.map r ≫ F.map m) ≫ e := congrArg (fun z => z ≫ e) (F.map_comp r m)
    _ = F.map r ≫ (F.map m ≫ e) := Category.assoc _ _ _
    _ = F.map r ≫ (eta ≫ v) := congrArg (fun z => F.map r ≫ z) hm
    _ = (F.map r ≫ eta) ≫ v := (Category.assoc _ _ _).symm
    _ = (eta ≫ u) ≫ v := congrArg (fun z => z ≫ v) hr
    _ = eta ≫ (u ≫ v) := Category.assoc _ _ _
    _ = eta ≫ w := congrArg (fun z => eta ≫ z) hs

private theorem scalar_comp {X : Scheme.{u}} (M : X.Modules) (r x z : Γ(X, ⊤))
    (h : r * x = z) : globalSectionsSmul M r ≫ globalSectionsSmul M x =
      globalSectionsSmul M z :=
  (globalSectionsSmul_mul M x r).symm.trans
    (congrArg (globalSectionsSmul M) ((mul_comm x r).trans h))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "PolynomialSections: scalar_restrict_section"

private theorem scalar_restrict_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules)
    (e : (restrictFunctor f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (m : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (a : Γ(Y, ⊤)) (b c : Γ(X, ⊤))
    (hm : (restrictFunctor f).map m ≫ e = (restrictUnitIso f).hom ≫
      globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) b)
    (ha : f.appTop a * b = c) :
    (restrictFunctor f).map (m ≫ globalSectionsSmul M a) ≫ e =
      (restrictUnitIso f).hom ≫ globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) c :=
  source_weighted_functor (restrictFunctor f) (restrictUnitIso f).hom e m
    (globalSectionsSmul (SheafOfModules.unit Y.ringCatSheaf) a) (globalSectionsSmul M a)
    (globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) (f.appTop a))
    (globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) b)
    (globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) c)
    hm (globalSectionsSmul_naturality m a) (restrict_unit_scalar f a)
    (scalar_comp (SheafOfModules.unit X.ringCatSheaf) (f.appTop a) b c ha)

private theorem sum_functor {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) (hF : F.Additive)
    {I : Type w} (s : Finset I) {S M : C} {N : D}
    (m : I → (S ⟶ M)) (eta : F.obj S ⟶ N) (e : F.obj M ⟶ N)
    (v : I → (N ⟶ N)) (hm : ∀ i ∈ s, F.map (m i) ≫ e = eta ≫ v i) :
    F.map (∑ i ∈ s, m i) ≫ e = eta ≫ ∑ i ∈ s, v i := by
  let _ := hF
  rw [F.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  exact Finset.sum_congr rfl hm

private theorem scalar_sum {X : Scheme.{u}} (M : X.Modules) {I : Type v}
    (s : Finset I) (r : I → Γ(X, ⊤)) :
    globalSectionsSmul M (∑ i ∈ s, r i) = ∑ i ∈ s, globalSectionsSmul M (r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, globalSectionsSmul_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, globalSectionsSmul_add, ih]

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "PolynomialSections: scalar_restrict_sum"

private theorem scalar_restrict_sum {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {I : Type v} (s : Finset I) (M : Y.Modules)
    (e : (restrictFunctor f).obj M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (m : I → ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M))
    (a : I → Γ(Y, ⊤)) (b c : I → Γ(X, ⊤)) (z : Γ(X, ⊤))
    (hm : ∀ i ∈ s, (restrictFunctor f).map (m i) ≫ e =
      (restrictUnitIso f).hom ≫ globalSectionsSmul ((SheafOfModules.unit X.ringCatSheaf :
        X.Modules)) (b i))
    (ha : ∀ i ∈ s, f.appTop (a i) * b i = c i) (hs : (∑ i ∈ s, c i) = z)
    (U : X.Opens)
    (x : ((restrictFunctor f).obj ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules))).val.obj (op
      U)) :
    (((restrictFunctor f).map (@Finset.sum I
      ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ M)
      (@Preadditive.homGroup Y.Modules inferInstance (inferInstance : Preadditive Y.Modules)
        (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) M).toAddCommMonoid
      s (fun i => m i ≫ globalSectionsSmul M (a i))) ≫ e).val.app (op U)).hom x =
      (((restrictUnitIso f).hom ≫ globalSectionsSmul
        ((SheafOfModules.unit X.ringCatSheaf : X.Modules)) z).val.app (op U)).hom x := by
  let N : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let eta : (restrictFunctor f).obj (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ N :=
    (restrictUnitIso f).hom
  have hw : ∀ i ∈ s, (restrictFunctor f).map (m i ≫ globalSectionsSmul M (a i)) ≫ e =
      eta ≫ globalSectionsSmul N (c i) := by
    intro i hi
    exact scalar_restrict_section f M e (m i) (a i) (b i) (c i) (hm i hi) (ha i hi)
  have h := sum_functor (restrictFunctor f) (restrictAdditive f) s
    (fun i => m i ≫ globalSectionsSmul M (a i)) eta e
    (fun i => globalSectionsSmul N (c i)) hw
  have h' := h.trans ((congrArg (fun t => eta ≫ t) (scalar_sum N s c).symm).trans
    (congrArg (fun r => eta ≫ globalSectionsSmul N r) hs))
  exact congrArg
    (fun q : (restrictFunctor f).obj ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) ⟶ N =>
      (q.val.app (op U)).hom x) h'

private theorem spec_scalar {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      (Scheme.ΓSpecIso (.of B)).inv (f a) :=
  (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) a).symm

private theorem comp_scalar {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : Γ(Z, ⊤)) : (f ≫ g).appTop r = f.appTop (g.appTop r) := rfl

private def baseScalar (R : Type u) [CommRing R] (a : R) : Γ(line R, ⊤) :=
  (projectiveToSpec R (ULift.{u} (Fin 2))).appTop ((Scheme.ΓSpecIso (.of R)).inv a)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "PolynomialSections: baseScalar_chart"

private theorem baseScalar_chart (R : Type u) [CommRing R] (a : R) :
    (chart R ⟨0⟩).appTop (baseScalar R a) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.C a) :=
  (comp_scalar (chart R ⟨0⟩) (projectiveToSpec R (ULift.{u} (Fin 2)))
    ((Scheme.ΓSpecIso (.of R)).inv a)).symm.trans
      ((congrArg (fun f : affine R ⟶ Spec (.of R) =>
        f.appTop ((Scheme.ΓSpecIso (.of R)).inv a))
          (projectiveLinePolynomialChart_base R ⟨0⟩)).trans (spec_scalar Polynomial.C a))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "PolynomialSections: monomialScalar"
    (← IO.getStderr).flush

private theorem monomialScalar (R : Type u) [CommRing R] (k : ℕ) (a : R) :
    (chart R ⟨0⟩).appTop (baseScalar R a) *
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.X ^ k) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.C a * Polynomial.X ^ k) :=
  (congrArg (fun z => z * (Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.X ^ k))
    (baseScalar_chart R a)).trans
      ((Scheme.ΓSpecIso (.of (Polynomial R))).inv.hom.map_mul _ _).symm

private theorem supportExpansion {R : Type u} [CommRing R] (P : Polynomial R) :
    (P.support.attach.sum fun k => Polynomial.C (P.coeff k.val) * Polynomial.X ^ k.val) = P :=
  (Finset.sum_attach P.support (fun k => Polynomial.C (P.coeff k) * Polynomial.X ^ k)).trans
    (by simpa only [Polynomial.sum] using Polynomial.sum_C_mul_X_pow_eq P)

/-- A polynomial of degree at most d gives a global section of the transition module of degree d. -/
def projectivePolynomialSection (R : Type u) [CommRing R] (d : ℕ)
    (P : Polynomial R) (hP : P.natDegree ≤ d) :
    structureModule (line R) ⟶ projectiveTransitionModule R d :=
  P.support.attach.sum fun k =>
    projectiveMonomialSection R d k.val
        ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp k.property)).trans hP) ≫
      globalSectionsSmul (projectiveTransitionModule R d) (baseScalar R (P.coeff k.val))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "PolynomialSections: projectivePolynomialSection_left"

/-- The positive coordinate of the global polynomial section is the original polynomial. -/
theorem projectivePolynomialSection_left (R : Type u) [CommRing R] (d : ℕ)
    (P : Polynomial R) (hP : P.natDegree ≤ d) :
    (restrictFunctor (chart R ⟨0⟩)).map (projectivePolynomialSection R d P hP) ≫
        (projectiveTransitionChart R d ⟨0⟩).hom =
      (restrictUnitIso (chart R ⟨0⟩)).hom ≫ globalSectionsSmul (structureModule (affine R))
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv P) := by
  classical
  have hs : P.support.attach.sum (fun k =>
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv
        (Polynomial.C (P.coeff k.val) * Polynomial.X ^ k.val)) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv P := by
    exact (map_sum (Scheme.ΓSpecIso (.of (Polynomial R))).inv.hom _ _).symm.trans
      (congrArg (fun Q : Polynomial R => (Scheme.ΓSpecIso (.of (Polynomial R))).inv Q)
        (supportExpansion P))
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact scalar_restrict_sum (chart R ⟨0⟩) P.support.attach (projectiveTransitionModule R d)
    (projectiveTransitionChart R d ⟨0⟩).hom
    (fun k => projectiveMonomialSection R d k.val
      ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp k.property)).trans hP))
    (fun k => baseScalar R (P.coeff k.val))
    (fun k => (Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.X ^ k.val))
    (fun k => (Scheme.ΓSpecIso (.of (Polynomial R))).inv
      (Polynomial.C (P.coeff k.val) * Polynomial.X ^ k.val))
    ((Scheme.ΓSpecIso (.of (Polynomial R))).inv P)
    (fun k _ => projectiveMonomial_left R d k.val
      ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp k.property)).trans hP))
    (fun k _ => monomialScalar R k.val (P.coeff k.val)) hs U.unop x

end SchubertGeometry.ProjectiveLine
