import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarLocalization
import OrbitComplexity.FrobeniusSplitting.Normality.PresentationGraphs
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImages
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# Principal localization graphs

Finite graphs record the coefficient and generic algebras of principal patches.
-/

open CategoryTheory
open scoped TensorProduct

namespace FrobeniusSplitting

universe u v w

namespace PrincipalDiagram

/-- An arrow together with its source and target in the algebra diagram. -/
abbrev DiagramArrow (C : Type v) [Category.{w} C] := Σ i : C, Σ j : C, i ⟶ j

/-- A chosen principal localization attached to an arrow. -/
abbrev PrincipalPatch {C : Type v} [Category.{w} C]
    (L : DiagramArrow C → Type u) := Σ b, L b

/-- The diagram objects and both localizations for each chosen principal patch. -/
abbrev PrincipalNode {C : Type v} [Category.{w} C]
    (L : DiagramArrow C → Type u) := C ⊕ (PrincipalPatch L × Bool)

variable {C : Type v} [Category.{w} C] {K : Type u} [CommRing K]
    {S : Subalgebra ℤ K} (D₀ : C ⥤ CommAlgCat.{u} S) (D : C ⥤ CommAlgCat.{u} K)
    (L : DiagramArrow C → Type u)
    (g : ∀ b, L b → D₀.obj b.1) (a : ∀ b, L b → D.obj b.1)

/-- The coefficient algebra at an object or a chosen principal patch. -/
def modelAt : PrincipalNode L → Type u
  | .inl i => D₀.obj i
  | .inr (⟨b, j⟩, false) => Localization.Away (g b j)
  | .inr (⟨b, j⟩, true) => Localization.Away ((D₀.map b.2.2).hom (g b j))

private instance modelAtRing (n : PrincipalNode L) : CommRing (modelAt D₀ L g n) := by
  rcases n with i | ⟨⟨b, j⟩, c⟩
  · change CommRing (D₀.obj i)
    infer_instance
  · cases c <;> dsimp only [modelAt] <;> infer_instance

private instance modelAtAlgebra (n : PrincipalNode L) : Algebra S (modelAt D₀ L g n) := by
  rcases n with i | ⟨⟨b, j⟩, c⟩
  · change Algebra S (D₀.obj i)
    infer_instance
  · cases c <;> dsimp only [modelAt] <;> infer_instance

private theorem modelAt_finite [∀ i, Algebra.FinitePresentation S (D₀.obj i)]
    (n : PrincipalNode L) : Algebra.FinitePresentation S (modelAt D₀ L g n) := by
  rcases n with i | ⟨⟨b, j⟩, c⟩
  · change Algebra.FinitePresentation S (D₀.obj i)
    infer_instance
  · cases c
    · change Algebra.FinitePresentation S (Localization.Away (g b j))
      exact Algebra.FinitePresentation.trans S (D₀.obj b.1) _
    · change Algebra.FinitePresentation S
        (Localization.Away ((D₀.map b.2.2).hom (g b j)))
      exact Algebra.FinitePresentation.trans S (D₀.obj b.2.1) _

/-- The generic algebra at an object or a chosen principal patch. -/
def genericAt : PrincipalNode L → Type u
  | .inl i => D.obj i
  | .inr (⟨b, j⟩, false) => Localization.Away (a b j)
  | .inr (⟨b, j⟩, true) => Localization.Away ((D.map b.2.2).hom (a b j))

private instance genericAtRing (n : PrincipalNode L) : CommRing (genericAt D L a n) := by
  rcases n with i | ⟨⟨b, j⟩, c⟩
  · change CommRing (D.obj i)
    infer_instance
  · cases c <;> dsimp only [genericAt] <;> infer_instance

private instance genericAtAlgebra (n : PrincipalNode L) : Algebra K (genericAt D L a n) := by
  rcases n with i | ⟨⟨b, j⟩, c⟩
  · change Algebra K (D.obj i)
    infer_instance
  · cases c <;> dsimp only [genericAt] <;> infer_instance

/-- Scalar comparisons on objects extend to their chosen principal localizations. -/
noncomputable def localizationComparisons
    (e : ∀ i, K ⊗[S] D₀.obj i ≃ₐ[K] D.obj i)
    (hnatural : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (D₀.map f).hom) =
      (D.map f).hom.comp (e i).toAlgHom)
    (hg : ∀ b j, e b.1 ((1 : K) ⊗ₜ[S] g b j) = a b j) :
    ∀ n, K ⊗[S] modelAt D₀ L g n ≃ₐ[K] genericAt D L a n
  | .inl i => e i
  | .inr (⟨b, j⟩, false) => localizationScalarEquiv (B := Localization.Away (a b j))
      (e b.1) (g b j) (a b j) (hg b j)
  | .inr (⟨b, j⟩, true) => localizationScalarEquiv
      (B := Localization.Away ((D.map b.2.2).hom (a b j))) (e b.2.1)
      ((D₀.map b.2.2).hom (g b j)) ((D.map b.2.2).hom (a b j)) (by
        have h := AlgHom.congr_fun (hnatural b.1 b.2.1 b.2.2) ((1 : K) ⊗ₜ[S] g b j)
        change e b.2.1 ((1 : K) ⊗ₜ[S] (D₀.map b.2.2).hom (g b j)) =
          (D.map b.2.2).hom (e b.1 ((1 : K) ⊗ₜ[S] g b j)) at h
        exact h.trans (congrArg (D.map b.2.2).hom (hg b j)))

/-- The diagram arrows, localization maps, and two directions of patch identifications. -/
abbrev PrincipalEdge {C : Type v} [Category.{w} C]
    (L : DiagramArrow C → Type u) := DiagramArrow C ⊕ (PrincipalPatch L × (Bool ⊕ Bool))

/-- The source object of an arrow in the principal localization graph. -/
def edgeSrc : PrincipalEdge L → PrincipalNode L
  | .inl b => .inl b.1
  | .inr (⟨b, _⟩, .inl false) => .inl b.1
  | .inr (⟨b, _⟩, .inl true) => .inl b.2.1
  | .inr (p, .inr c) => .inr (p, c)

/-- The target object of an arrow in the principal localization graph. -/
def edgeTgt : PrincipalEdge L → PrincipalNode L
  | .inl b => .inl b.2.1
  | .inr (p, .inl c) => .inr (p, c)
  | .inr (p, .inr c) => .inr (p, !c)

/-- The maps and inverse patch identifications of the generic localization graph. -/
noncomputable def genericMaps
    (hlocal : ∀ b j,
      Function.Bijective (Localization.awayMap (D.map b.2.2).hom.toRingHom (a b j))) :
    ∀ b : PrincipalEdge L,
      genericAt D L a (edgeSrc L b) →ₐ[K] genericAt D L a (edgeTgt L b)
  | .inl b => (D.map b.2.2).hom
  | .inr (⟨b, j⟩, .inl false) =>
      IsScalarTower.toAlgHom K (D.obj b.1) (Localization.Away (a b j))
  | .inr (⟨b, j⟩, .inl true) =>
      IsScalarTower.toAlgHom K (D.obj b.2.1)
        (Localization.Away ((D.map b.2.2).hom (a b j)))
  | .inr (⟨b, j⟩, .inr false) => Localization.awayMapₐ (D.map b.2.2).hom (a b j)
  | .inr (⟨b, j⟩, .inr true) =>
      (AlgEquiv.ofBijective (Localization.awayMapₐ (D.map b.2.2).hom (a b j))
        (hlocal b j)).symm.toAlgHom

/-- The finite indices of unit-cover coefficients retained at each graph object. -/
def coefficientIndex : PrincipalNode L → Type (max u v w)
  | .inl i => Σ j : C, Σ f : j ⟶ i, L ⟨j, i, f⟩
  | .inr _ => PEmpty

private instance coefficientIndex_finite [Finite C] [∀ i j : C, Finite (i ⟶ j)]
    [∀ b, Finite (L b)] (n : PrincipalNode L) : Finite (coefficientIndex L n) := by
  rcases n with i | p
  · change Finite (Σ j : C, Σ f : j ⟶ i, L ⟨j, i, f⟩)
    infer_instance
  · change Finite PEmpty
    infer_instance

/-- The unit-cover coefficients regarded as elements of the localization graph. -/
def graphElements (c : ∀ b, L b → D.obj b.2.1) :
    ∀ n, coefficientIndex L n → genericAt D L a n
  | .inl i => fun j ↦ c ⟨j.1, i, j.2.1⟩ j.2.2
  | .inr _ => fun j ↦ nomatch j

private def smoothAt (smoothNodes : Set C) : Set (PrincipalNode L)
  | .inl i => i ∈ smoothNodes
  | .inr _ => False

private theorem modelAt_smooth (smoothNodes : Set C)
    (hsm : ∀ i ∈ smoothNodes, Algebra.Smooth S (D₀.obj i))
    (n : PrincipalNode L) (hn : n ∈ smoothAt L smoothNodes) :
    Algebra.Smooth S (modelAt D₀ L g n) := by
  rcases n with i | p
  · exact hsm i hn
  · exact False.elim hn

/-- One coefficient ring retains a principal localization graph and chosen elements. -/
theorem exists_localization_images
    [Finite C] [∀ i j : C, Finite (i ⟶ j)] [∀ b, Finite (L b)]
    [∀ i, Algebra.FinitePresentation S (D₀.obj i)] (hS : S.FG)
    (e : ∀ i, K ⊗[S] D₀.obj i ≃ₐ[K] D.obj i)
    (hnatural : ∀ i j (f : i ⟶ j), (e j).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (D₀.map f).hom) =
      (D.map f).hom.comp (e i).toAlgHom)
    (hg : ∀ b j, e b.1 ((1 : K) ⊗ₜ[S] g b j) = a b j)
    (maps : ∀ b : PrincipalEdge L,
      genericAt D L a (edgeSrc L b) →ₐ[K] genericAt D L a (edgeTgt L b))
    (smoothNodes : Set C) (hsm : ∀ i ∈ smoothNodes, Algebra.Smooth S (D₀.obj i))
    (c : ∀ b, L b → D.obj b.2.1)
    (J : PrincipalNode L → Type*) [∀ n, Finite (J n)]
    (elements : ∀ n, J n → genericAt D L a n) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      ∃ (models : ∀ n, Subalgebra R (genericAt D L a n))
        (comparison : ∀ n, K ⊗[R] models n ≃ₐ[K] genericAt D L a n),
        R.FG ∧
        (∀ n, models n = (scalarImageHom (R := R)
          (localizationComparisons D₀ D L g a e hnatural hg n)).range) ∧
        (∀ n, Algebra.FinitePresentation R (models n)) ∧
        (∀ i, i ∈ smoothNodes → Algebra.Smooth R (models (.inl i))) ∧
        (∀ n (k : K) (m : models n),
          comparison n (k ⊗ₜ[R] m) = algebraMap K (genericAt D L a n) k * (m : genericAt D L a n)) ∧
        (∀ (b : PrincipalEdge L) (x : models (edgeSrc L b)),
          maps b (x : genericAt D L a (edgeSrc L b)) ∈
            models (edgeTgt L b)) ∧
        (∀ n j, graphElements D L a c n j ∈ models n) ∧
        ∀ n j, elements n j ∈ models n := by
  classical
  have (n : PrincipalNode L) : Algebra.FinitePresentation S (modelAt D₀ L g n) :=
    modelAt_finite D₀ L g n
  let eM := localizationComparisons D₀ D L g a e hnatural hg
  let vars (n : PrincipalNode L) :=
    Fin (Algebra.Presentation.ofFinitePresentationVars S (modelAt D₀ L g n))
  let rels (n : PrincipalNode L) :=
    Fin (Algebra.Presentation.ofFinitePresentationRels S (modelAt D₀ L g n))
  let Q (n : PrincipalNode L) :
      Algebra.Presentation S (modelAt D₀ L g n) (vars n) (rels n) :=
    Algebra.Presentation.ofFinitePresentation S (modelAt D₀ L g n)
  obtain ⟨R, hP, models, comparison, hSR, hfg, hcanonical, hfp, hsmooth, heval,
    hmaps, helts⟩ := exists_presentation_image_graph S hS
      (modelAt D₀ L g) (genericAt D L a) vars rels Q eM (smoothAt L smoothNodes)
      (modelAt_smooth D₀ L g smoothNodes hsm) (edgeSrc L) (edgeTgt L)
      maps (fun n ↦ coefficientIndex L n ⊕ J n)
      (fun n ↦ Sum.elim (graphElements D L a c n) (elements n))
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  have : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  have (n : PrincipalNode L) : (((Q n).baseChange K).ofAlgEquiv (eM n)).HasCoeffs R := hP n
  refine ⟨R, hSR, models, comparison, hfg, ?_, hfp,
    (fun i hi ↦ hsmooth (.inl i) hi), heval, (fun b x ↦ hmaps b x.property),
    (fun n j ↦ helts n (.inl j)), (fun n j ↦ helts n (.inr j))⟩
  intro n
  exact (hcanonical n).trans
    (modelImage_eq_scalarImage (Q n) (eM n) (FaithfulSMul.algebraMap_injective R K))


end PrincipalDiagram

end FrobeniusSplitting
