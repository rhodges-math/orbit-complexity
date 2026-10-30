import OrbitComplexity.FrobeniusSplitting.Normality.Images.ChosenGraph
import OrbitComplexity.FrobeniusSplitting.Normality.Models.TransitionLifts
import OrbitComplexity.FrobeniusSplitting.Normality.FixedFibreDiagrams
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImages
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelCoefficients
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelNaturality
import Mathlib.RingTheory.Smooth.Flat

/-! # Borel transitions on the base change of the chosen coordinate diagram -/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions FrobeniusSplitting
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u v
namespace SchubertGeometry

private theorem scalar_evaluation_injective {S R K M A : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing A]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Module.Flat S M] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (e : K ⊗[S] M ≃ₐ[K] A) (hi : Function.Injective (algebraMap R K)) :
    Function.Injective (scalarImageHom (R := R) e) := by
  apply e.injective.comp
  change Function.Injective (((Algebra.ofId R K).restrictScalars S).toLinearMap.rTensor M)
  exact Module.Flat.rTensor_preserves_injective_linearMap _ hi

/-- All Borel parameters descend on one coefficient extension of the chosen
smooth intersection diagram, with its original arrows, cocycles and restrictions. -/
theorem exists_chosen_borel_transitions {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (i : G.rootBase.support) {J : Type v} [Finite J]
    (S : Subalgebra ℤ K) (hS : S.FG)
    (M : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [∀ s, Algebra.FinitePresentation S (M.obj s)] [∀ s, Algebra.Smooth S (M.obj s)]
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[S] M.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (M.map f).hom) =
      (F.map f).hom.comp (e s).toAlgHom)
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hnatural : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk) :
    let c := fun s j hj k hk ↦
      Units.map (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
        (simpleRootCoefficient G i)
    let a := fun s j hj k hk ↦
      simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
        ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      let N := fixedFibreDiagram (R := R) (M := R) M
      ∃ v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
          F ⋙ forget₂ (CommAlgCat K) CommRingCat,
        R.FG ∧
        (∀ s x, (v.app s).hom x = e s
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
            (AlgHom.id S (M.obj s)) x)) ∧ transitionLiftSpec N F v c a := by
  classical
  let I := {s : Finset J // s.Nonempty}
  let c := fun s j hj k hk ↦
    Units.map (simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)).toRingHom.toMonoidHom
      (simpleRootCoefficient G i)
  let a := fun s j hj k hk ↦
    simpleBorelCoefficientMap G i (F.obj s) (beta s j hj k hk)
      ((simpleRootCoefficient G i : simpleBorelCoefficientAlgebra G) * simpleRootParameter G)
  let vars (s : I) := Fin (Algebra.Presentation.ofFinitePresentationVars S (M.obj s))
  let rels (s : I) := Fin (Algebra.Presentation.ofFinitePresentationRels S (M.obj s))
  let Q (s : I) : Algebra.Presentation S (M.obj s) (vars s) (rels s) :=
    Algebra.Presentation.ofFinitePresentation S (M.obj s)
  let L (s : I) := {j : J // j ∈ s.val} × {k : J // k ∈ s.val} × Fin 3
  let values (s : I) (x : L s) : F.obj s :=
    if x.2.2 = 0 then c s x.1.val x.1.property x.2.1.val x.2.1.property else
    if x.2.2 = 1 then ↑((c s x.1.val x.1.property x.2.1.val x.2.1.property)⁻¹) else
      a s x.1.val x.1.property x.2.1.val x.2.1.property
  obtain ⟨R, hSR, _, hR, _, hvalues⟩ := exists_chosen_graph_elements S hS
    (fun s ↦ M.obj s) (fun s ↦ (F.obj s : Type u)) e vars rels Q
    (fun b : Empty ↦ nomatch b) (fun b : Empty ↦ nomatch b)
    (fun b : Empty ↦ nomatch b) L values
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let N := fixedFibreDiagram (R := R) (M := R) M
  let v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat :=
    { app := fun s ↦ CommRingCat.ofHom (scalarImageHom (R := R) (e s)).toRingHom
      naturality := by
        intro s t f
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro x
        induction x using TensorProduct.inductionOn with
        | tmul r x => exact AlgHom.congr_fun (he s t f) (algebraMap R K r ⊗ₜ[S] x)
        | add x y hx hy => simp only [map_add, hx, hy] }
  have hv (s : I) (x : N.obj s) : (v.app s).hom x = e s
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
        (AlgHom.id S (M.obj s)) x) := rfl
  have hi (s : I) : Function.Injective (v.app s).hom :=
    scalar_evaluation_injective (e s) (FaithfulSMul.algebraMap_injective R K)
  have hrange (s : I) (l : L s) : values s l ∈ Set.range (v.app s).hom := by
    obtain ⟨x, hx⟩ := hvalues s l
    exact ⟨x, (hv s x).trans hx⟩
  have hm (s : I) j hj k hk :
      (c s j hj k hk : F.obj s) ∈ Set.range (v.app s).hom ∧
      (↑((c s j hj k hk)⁻¹) : F.obj s) ∈ Set.range (v.app s).hom ∧
      a s j hj k hk ∈ Set.range (v.app s).hom := by
    constructor
    · simpa only [values, ↓reduceIte] using hrange s (⟨j, hj⟩, ⟨k, hk⟩, 0)
    constructor
    · simpa only [values, show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] using
        hrange s (⟨j, hj⟩, ⟨k, hk⟩, 1)
    · simpa only [values, show (2 : Fin 3) ≠ 0 by decide,
        show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte] using
          hrange s (⟨j, hj⟩, ⟨k, hk⟩, 2)
  have hco s j hj k hk l hl :
      c s j hj l hl = c s k hk l hl * c s j hj k hk ∧
      a s j hj l hl = (c s k hk l hl : F.obj s) * a s j hj k hk + a s k hk l hl :=
    (simpleBorelCoefficient_laws G i (F.obj s)).2.2.2
      (beta s j hj k hk) (beta s k hk l hl) (beta s j hj l hl) (hbeta s j hj k hk l hl)
  have hn s t (f : s ⟶ t) j hj k hk :
      Units.map (F.map f).hom.toRingHom.toMonoidHom (c s j hj k hk) =
        c t j ((leOfHom f) hj) k ((leOfHom f) hk) ∧
      (F.map f).hom (a s j hj k hk) = a t j ((leOfHom f) hj) k ((leOfHom f) hk) := by
    have H := (simpleBorelCoefficient_natural G i (F.obj s) (F.obj t)
      (F.map f).hom (beta s j hj k hk)).2
    rw [CommAlgCat.ofHom_hom, ← hnatural] at H
    exact ⟨H.1.symm, H.2.symm⟩
  exact ⟨R, hSR, v, hR, hv, exists_transition_lifts N F v hi c a hm hco hn⟩

end SchubertGeometry
