import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedNormalization
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedRightProjection
import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialBoundary
import OrbitComplexity.FrobeniusSplitting.Compatible.Morphisms
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Compatibility of the infinity section with the relative Cartier splitting -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting

noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

open private indices line relativeBase sourceLine unitLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private insertedInfinity
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections
open private sectionWeight chartOpen
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
open private naturality_of_restrict
  from OrbitComplexity.SchubertGeometry.Frobenius.ProjectiveCovariance

private theorem compatible_kernel {X Y : Scheme.{u}} {q : ℕ}
    (σ : SchemeSplitting Y q) (τ : SchemeFrobeniusMap X q)
    (f : X ⟶ Y) [QuasiCompact f]
    (hf : ∀ U s, τ.onOpen (f ⁻¹ᵁ U) (f.app U s) = f.app U (σ.onOpen U s)) :
    σ.IsCompatible f.ker := by
  intro U a ha
  rw [f.ker_apply U] at ha ⊢
  apply RingHom.mem_ker.mpr
  have hz : f.app U a = 0 := RingHom.mem_ker.mp ha
  exact ((hf U a).symm.trans (congrArg (τ.onOpen (f ⁻¹ᵁ U)) hz)).trans
    (FrobeniusLinearMap.map_zero (τ.onOpen (f ⁻¹ᵁ U)))

private theorem naturality_comp {X Y Z : Scheme.{u}} {q : ℕ}
    (τ : SchemeFrobeniusMap X q) (σ : SchemeFrobeniusMap Y q)
    (φ : SchemeFrobeniusMap Z q) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ U s, τ.onOpen (f ⁻¹ᵁ U) (f.app U s) = f.app U (σ.onOpen U s))
    (hg : ∀ U s, σ.onOpen (g ⁻¹ᵁ U) (g.app U s) = g.app U (φ.onOpen U s))
    (U : Z.Opens) (s : Γ(Z, U)) :
    τ.onOpen ((f ≫ g) ⁻¹ᵁ U) ((f ≫ g).app U s) =
      (f ≫ g).app U (φ.onOpen U s) := by
  change τ.onOpen (f ⁻¹ᵁ (g ⁻¹ᵁ U)) (f.app (g ⁻¹ᵁ U) (g.app U s)) =
    f.app (g ⁻¹ᵁ U) (g.app U (φ.onOpen U s))
  exact (hf (g ⁻¹ᵁ U) (g.app U s)).trans (congrArg (f.app (g ⁻¹ᵁ U)) (hg U s))

private theorem normalized_value {X : Scheme.{u}} {q : ℕ}
    (θ φ : SchemeFrobeniusMap X q) (h : θ = φ) (hθ : θ.onOpen ⊤ 1 = 1)
    (U : X.Opens) (s : Γ(X, U)) :
    (θ.toSplitting 1 hθ).onOpen U s = φ.onOpen U s := by
  refine (SchemeFrobeniusMap.toSplitting_apply θ 1 hθ U s).trans ?_
  have hmul : X.presheaf.map (homOfLE le_top).op (1 : Γ(X, ⊤)) * s = s := by
    rw [map_one, one_mul]
  exact (congrArg (θ.onOpen U) hmul).trans (congrArg (fun t => t.onOpen U s) h)

private theorem normalized_kernel {X Y : Scheme.{u}} {q : ℕ}
    (θ φ : SchemeFrobeniusMap Y q) (h : θ = φ) (hθ : θ.onOpen ⊤ 1 = 1)
    (τ : SchemeFrobeniusMap X q) (f : X ⟶ Y) [QuasiCompact f]
    (hf : ∀ U s, τ.onOpen (f ⁻¹ᵁ U) (f.app U s) = f.app U (φ.onOpen U s)) :
    (θ.toSplitting 1 hθ).IsCompatible f.ker := by
  apply compatible_kernel (θ.toSplitting 1 hθ) τ f
  intro U s
  exact (hf U s).trans
    (congrArg (f.app U) (normalized_value θ φ h hθ U s).symm)

private theorem weight_spec_eq {R : Type u} [CommRing R] {q : ℕ}
    (ψ : FrobeniusLinearMap R q) (a b : R) (h : a = b) (hq : 0 < q) :
    (ψ.weight a).toSpec hq = (ψ.weight b).toSpec hq :=
  congrArg (fun r => (ψ.weight r).toSpec hq) h

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

private theorem polynomial_zero_natural (ψ : FrobeniusLinearMap A p)
    (Q : Polynomial A) (U : (Spec (.of (Polynomial A))).Opens)
    (s : Γ(Spec (.of (Polynomial A)), U)) :
    ((ψ.weight (Q.eval 0)).toSpec (expChar_pos K p)).onOpen
        ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A)))) ⁻¹ᵁ U)
        ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A)))).app U s) =
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A)))).app U
        ((((polynomialTraceOfOperator (K := K) ψ).weight
          (Q * Polynomial.X ^ (p - 1))).toSpec (expChar_pos K p)).onOpen U s) := by
  apply FrobeniusLinearMap.toSpec_naturality
  intro f
  exact (polynomialTrace_weight_eval_zero (K := K) ψ Q f).symm

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RelativeTwistedBoundary: negative_chart_natural"

private theorem negative_chart_natural (ψ : FrobeniusLinearMap A p)
    (s : (ProjectiveLine.projectiveTransitionModule A (2 * (p - 1))).val.obj (op ⊤))
    (Q : Polynomial A)
    (hQ : sectionWeight s (⟨1⟩ : indices.{u}) = Q * Polynomial.X ^ (p - 1))
    (U : (line A).Opens) (a : Γ(line A, U)) :
    (((polynomialTraceOfOperator (K := K) ψ).weight
      (Q * Polynomial.X ^ (p - 1))).toSpec (expChar_pos K p)).onOpen
        ((projectiveLinePolynomialChart A (⟨1⟩ : indices.{u})) ⁻¹ᵁ U)
        ((projectiveLinePolynomialChart A (⟨1⟩ : indices.{u})).app U a) =
      (projectiveLinePolynomialChart A (⟨1⟩ : indices.{u})).app U
        ((relativeCartierOperator (K := K) ψ s).onOpen U a) := by
  have hc := relativeCartierOperator_chart (K := K) ψ s (⟨1⟩ : indices.{u})
  have hw := weight_spec_eq (polynomialTraceOfOperator (K := K) ψ)
    (sectionWeight s (⟨1⟩ : indices.{u})) (Q * Polynomial.X ^ (p - 1))
    hQ (expChar_pos K p)
  have he := hc.trans (congrArg
    (fun τ => τ.pushforward (projectiveLinePolynomialIso A (⟨1⟩ : indices.{u})).hom) hw)
  exact naturality_of_restrict (relativeCartierOperator (K := K) ψ s)
    (chartOpen A (⟨1⟩ : indices.{u}))
    (projectiveLinePolynomialIso A (⟨1⟩ : indices.{u})) _ he U a

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "RelativeTwistedBoundary: relativeTwistedSection_infinity"

/-- The splitting obtained from the relative Cartier map preserves the infinity section. -/
theorem relativeTwistedSection_infinity (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p))
    (P : Polynomial A)
    (hP : sectionWeight (insertedInfinity m) (⟨0⟩ : indices.{u}) = P)
    (hdegree : P.natDegree < p + (p - 1)) (hnorm : ψ (P.coeff (p - 1)) = 1) :
    (relativeTwistedSectionSplitting (K := K) ψ m P hP hdegree hnorm).IsCompatible
      (projectiveLineSection A (⟨1⟩ : indices.{u})).ker := by
  let Q : Polynomial A := (Scheme.ΓSpecIso (.of (Polynomial A))).hom
    (((m ≫ pullback.snd (ProjectiveLine.leftRestriction A)
      (ProjectiveLine.twistedRestriction A (p - 1))).val.app (op ⊤)).hom
        (1 : Γ(line A, ⊤)))
  have hQ : sectionWeight (insertedInfinity m) (⟨1⟩ : indices.{u}) =
      Q * Polynomial.X ^ (p - 1) := insertedInfinity_right m
  have hc := negative_chart_natural (K := K) ψ (insertedInfinity m) Q hQ
  have he := polynomial_zero_natural (K := K) ψ Q
  have hn := naturality_comp
    ((ψ.weight (Q.eval 0)).toSpec (expChar_pos K p))
    (((polynomialTraceOfOperator (K := K) ψ).weight
      (Q * Polynomial.X ^ (p - 1))).toSpec (expChar_pos K p))
    (relativeCartierOperator (K := K) ψ (insertedInfinity m))
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A))))
    (projectiveLinePolynomialChart A (⟨1⟩ : indices.{u})) he hc
  exact normalized_kernel _ _ (twistedSectionOperator_relative (K := K) ψ m)
    (relativeTwistedOperator_one (K := K) ψ m P hP hdegree hnorm)
    ((ψ.weight (Q.eval 0)).toSpec (expChar_pos K p))
    (projectiveLineSection A (⟨1⟩ : indices.{u})) hn


end SchubertGeometry.ProjectiveCartier
