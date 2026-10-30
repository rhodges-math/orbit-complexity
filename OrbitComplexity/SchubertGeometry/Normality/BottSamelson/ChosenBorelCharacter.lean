import OrbitComplexity.FrobeniusSplitting.Normality.Images.ChosenGraph
import OrbitComplexity.FrobeniusSplitting.Normality.Models.FixedModelComparison
import OrbitComplexity.FrobeniusSplitting.Normality.Models.ModelTransitionLifts
import OrbitComplexity.SchubertGeometry.Frobenius.BorelSectionCharacter
import Mathlib.RingTheory.Flat.Stability

/-! # The full positive-root character in the same chosen coefficient diagram -/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions FrobeniusSplitting
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u v
namespace SchubertGeometry

private theorem character_lifts {I : Type v} {R K : Type u}
    [CommRing R] [CommRing K]
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (hi : ∀ s, Function.Injective (e.app s).hom)
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (hm : ∀ s j hj k hk,
      (c s j hj k hk : F.obj s) ∈ Set.range (e.app s).hom ∧
      (↑((c s j hj k hk)⁻¹) : F.obj s) ∈ Set.range (e.app s).hom)
    (hco : ∀ s j hj k hk l hl,
      c s j hj l hl = c s k hk l hl * c s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toRingHom.toMonoidHom (c s j hj k hk) =
        c t j ((leOfHom f) hj) k ((leOfHom f) hk)) :
    ∃ c₀ : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (N.obj s)ˣ,
      (∀ s j hj k hk, (e.app s).hom (c₀ s j hj k hk : N.obj s) =
        (c s j hj k hk : F.obj s)) ∧
      (∀ s j hj k hk l hl,
        c₀ s j hj l hl = c₀ s k hk l hl * c₀ s j hj k hk) ∧
      (∀ s t (f : s ⟶ t) j hj k hk,
        Units.map (N.map f).hom.toMonoidHom (c₀ s j hj k hk) =
          c₀ t j ((leOfHom f) hj) k ((leOfHom f) hk)) ∧
      (∀ s j hj, c₀ s j hj j hj = 1) ∧
      (∀ s j hj k hk, c₀ s k hk j hj = (c₀ s j hj k hk)⁻¹) ∧
      ∀ n : ℕ,
        (∀ s j hj k hk,
          (e.app s).hom ((c₀ s j hj k hk : N.obj s) ^ n) =
            (c s j hj k hk : F.obj s) ^ n) ∧
        (∀ s j hj k hk l hl,
          (c₀ s j hj l hl) ^ n =
            (c₀ s k hk l hl) ^ n * (c₀ s j hj k hk) ^ n) ∧
        ∀ s t (f : s ⟶ t) j hj k hk,
          Units.map (N.map f).hom.toMonoidHom ((c₀ s j hj k hk) ^ n) =
            (c₀ t j ((leOfHom f) hj) k ((leOfHom f) hk)) ^ n := by
  have hm' s j hj k hk :
      (c s j hj k hk : F.obj s) ∈ Set.range (e.app s).hom ∧
      (↑((c s j hj k hk)⁻¹) : F.obj s) ∈ Set.range (e.app s).hom ∧
      (0 : F.obj s) ∈ Set.range (e.app s).hom :=
    And.intro (hm s j hj k hk).1
      (And.intro (hm s j hj k hk).2 ⟨0, map_zero (e.app s).hom⟩)
  have hco' s j hj k hk l hl :
      c s j hj l hl = c s k hk l hl * c s j hj k hk ∧
      (0 : F.obj s) = (c s k hk l hl : F.obj s) * 0 + 0 :=
    ⟨hco s j hj k hk l hl, by simp⟩
  have hn' s t (f : s ⟶ t) j hj k hk :
      Units.map (F.map f).hom.toRingHom.toMonoidHom (c s j hj k hk) =
        c t j ((leOfHom f) hj) k ((leOfHom f) hk) ∧
      (F.map f).hom (0 : F.obj s) = 0 :=
    ⟨hn s t f j hj k hk, map_zero _⟩
  obtain ⟨c₀, _, hd, _, hco₀, hn₀⟩ := exists_transition_lifts
    N F e hi c (fun _ _ _ _ _ ↦ 0) hm' hco' hn'
  have hdiag s j hj : c₀ s j hj j hj = 1 :=
    mul_eq_left.mp (hco₀ s j hj j hj j hj).1.symm
  have hinv s j hj k hk : c₀ s k hk j hj = (c₀ s j hj k hk)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact ((hco₀ s j hj k hk j hj).1.symm).trans (hdiag s j hj)
  refine ⟨c₀, hd, (fun s j hj k hk l hl ↦ (hco₀ s j hj k hk l hl).1),
    (fun s t f j hj k hk ↦ (hn₀ s t f j hj k hk).1), hdiag, hinv, ?_⟩
  intro n
  refine ⟨?_, ?_, ?_⟩
  · intro s j hj k hk
    rw [map_pow, hd]
  · intro s j hj k hk l hl
    rw [(hco₀ s j hj k hk l hl).1, mul_pow]
  · intro s t f j hj k hk
    rw [map_pow, (hn₀ s t f j hj k hk).1]

private theorem section_character_natural {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
    (A B : CommAlgCat.{u} K) (f : A ⟶ B)
    (beta : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    Units.map f.hom.toRingHom.toMonoidHom
        (ProjectiveLine.positiveBorelSection G A beta) =
      ProjectiveLine.positiveBorelSection G B ((algSpec (.of K)).map f.op ≫ beta) := by
  exact (ProjectiveLine.positiveBorelSection_natural G f beta).symm

private theorem section_character_laws {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)
    {J : Type v} (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
        (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hnatural : ∀ s t (f : s ⟶ t) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      beta t j ((leOfHom f) hj) k ((leOfHom f) hk) =
        (algSpec (.of K)).map (F.map f).op ≫ beta s j hj k hk)
    (hbeta : ∀ s j hj k hk l hl,
      beta s j hj l hl = beta s k hk l hl * beta s j hj k hk) :
    let delta := fun s j hj k hk ↦
      ProjectiveLine.positiveBorelSection G (F.obj s) (beta s j hj k hk)
    (∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk) ∧
    ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toRingHom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk) := by
  dsimp only
  constructor
  · intro s j hj k hk l hl
    rw [hbeta s j hj k hk l hl, map_mul]
  · intro s t f j hj k hk
    have h := section_character_natural G (F.obj s) (F.obj t) (F.map f)
      (beta s j hj k hk)
    exact h.trans (congrArg (fun b ↦ ProjectiveLine.positiveBorelSection G (F.obj t) b)
      (hnatural s t f j hj k hk).symm)

set_option maxHeartbeats 400000 in
/-- One coefficient enlargement retains the full character and its inverse on
all Borel transitions. Every power uses that same enlargement. -/
theorem exists_chosen_borel_character {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {J : Type v} [Finite J]
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
    let delta := fun s j hj k hk ↦
      ProjectiveLine.positiveBorelSection G (F.obj s) (beta s j hj k hk)
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R),
      letI : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      letI : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
      let N := fixedFibreDiagram (R := R) (M := R) M
      ∃ v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
          F ⋙ forget₂ (CommAlgCat K) CommRingCat,
        R.FG ∧
        (∀ s x, (v.app s).hom x = e s
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
            (AlgHom.id S (M.obj s)) x)) ∧
        ∃ delta₀ : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
          (k : J) (_ : k ∈ s.val), (N.obj s)ˣ,
          (∀ s j hj k hk,
            (v.app s).hom (delta₀ s j hj k hk : N.obj s) =
              (delta s j hj k hk : F.obj s)) ∧
          (∀ s j hj k hk l hl,
            delta₀ s j hj l hl = delta₀ s k hk l hl * delta₀ s j hj k hk) ∧
          (∀ s t (f : s ⟶ t) j hj k hk,
            Units.map (N.map f).hom.toMonoidHom (delta₀ s j hj k hk) =
              delta₀ t j ((leOfHom f) hj) k ((leOfHom f) hk)) ∧
          (∀ s j hj, delta₀ s j hj j hj = 1) ∧
          (∀ s j hj k hk, delta₀ s k hk j hj = (delta₀ s j hj k hk)⁻¹) ∧
          ∀ n : ℕ,
            (∀ s j hj k hk,
              (v.app s).hom ((delta₀ s j hj k hk : N.obj s) ^ n) =
                (delta s j hj k hk : F.obj s) ^ n) ∧
            (∀ s j hj k hk l hl,
              (delta₀ s j hj l hl) ^ n =
                (delta₀ s k hk l hl) ^ n * (delta₀ s j hj k hk) ^ n) ∧
            ∀ s t (f : s ⟶ t) j hj k hk,
              Units.map (N.map f).hom.toMonoidHom ((delta₀ s j hj k hk) ^ n) =
                (delta₀ t j ((leOfHom f) hj) k ((leOfHom f) hk)) ^ n := by
  classical
  let C := {s : Finset J // s.Nonempty}
  let delta := fun (s : C) j hj k hk ↦
    ProjectiveLine.positiveBorelSection G (F.obj s) (beta s j hj k hk)
  obtain ⟨hco, hn⟩ := section_character_laws G F beta hnatural hbeta
  dsimp only
  let vars (s : C) := Fin (Algebra.Presentation.ofFinitePresentationVars S (M.obj s))
  let rels (s : C) := Fin (Algebra.Presentation.ofFinitePresentationRels S (M.obj s))
  let Q (s : C) : Algebra.Presentation S (M.obj s) (vars s) (rels s) :=
    Algebra.Presentation.ofFinitePresentation S (M.obj s)
  let L (s : C) := {j : J // j ∈ s.val} × {k : J // k ∈ s.val} × Fin 2
  let values (s : C) (x : L s) : F.obj s :=
    if x.2.2 = 0 then (delta s x.1.val x.1.property x.2.1.val x.2.1.property : F.obj s)
    else (↑((delta s x.1.val x.1.property x.2.1.val x.2.1.property)⁻¹) : F.obj s)
  let noSrc : Empty → C := Empty.elim
  let noMaps : ∀ b : Empty, F.obj (noSrc b) →ₐ[K] F.obj (noSrc b) := fun b ↦ nomatch b
  obtain ⟨R, hSR, _, hR, _, hvalues⟩ := exists_chosen_graph_elements S hS
    (fun s : C ↦ M.obj s) (fun s : C ↦ F.obj s) e vars rels Q
    noSrc noSrc noMaps L values
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let N := fixedFibreDiagram (R := R) (M := R) M
  let eR : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s := fun s ↦
    (Algebra.TensorProduct.cancelBaseChange S R K K (M.obj s)).trans (e s)
  obtain ⟨heR, hvalue⟩ := fixed_model_comparison (R := R) M F e he
  let v := modelEvaluation N F eR heR
  have hv (s : C) (x : N.obj s) : (v.app s).hom x = e s
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S R K)
        (AlgHom.id S (M.obj s)) x) := hvalue s x
  have hi (s : C) : Function.Injective (v.app s).hom := by
    let : Module.Flat S (M.obj s) := inferInstance
    let : Module.Flat R (N.obj s) := by
      change Module.Flat R (R ⊗[S] M.obj s)
      infer_instance
    change Function.Injective (fun x : N.obj s ↦ eR s ((1 : K) ⊗ₜ[R] x))
    exact (eR s).injective.comp
      (Algebra.TensorProduct.includeRight_injective (R := R) (A := K) (B := N.obj s)
        (show Function.Injective (algebraMap R K) from Subtype.val_injective))
  have hm (s : C) j (hj : j ∈ s.val) k (hk : k ∈ s.val) :
      (delta s j hj k hk : F.obj s) ∈ Set.range (v.app s).hom ∧
      (↑((delta s j hj k hk)⁻¹) : F.obj s) ∈ Set.range (v.app s).hom := by
    obtain ⟨x, hx⟩ := hvalues s (⟨j, hj⟩, ⟨k, hk⟩, 0)
    obtain ⟨y, hy⟩ := hvalues s (⟨j, hj⟩, ⟨k, hk⟩, 1)
    have hxval : values s (⟨j, hj⟩, ⟨k, hk⟩, 0) =
        (delta s j hj k hk : F.obj s) := rfl
    have hyval : values s (⟨j, hj⟩, ⟨k, hk⟩, 1) =
        (↑((delta s j hj k hk)⁻¹) : F.obj s) := rfl
    exact ⟨⟨x, (hv s x).trans (hx.trans hxval)⟩,
      ⟨y, (hv s y).trans (hy.trans hyval)⟩⟩
  obtain ⟨delta₀, hd, hco₀, hn₀, hdiag, hinv, hpowers⟩ :=
    character_lifts N F v hi delta hm hco hn
  exact ⟨R, hSR, v, hR, hv, delta₀, hd, hco₀, hn₀, hdiag, hinv, hpowers⟩

end SchubertGeometry
