import OrbitComplexity.SchubertGeometry.Normality.Bundles.ProjectiveModelData
import OrbitComplexity.SchubertGeometry.Normality.Transitions.P1TransitionDiagram
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelCoefficients
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.BorelNaturality

/-! # Projective transitions in the same retained Borel coefficient model -/

open CategoryTheory AlgebraicGeometry FrobeniusSplitting ReductiveGroups GroupActions
open scoped TensorProduct CategoryTheory.MonObj
noncomputable section
universe u
namespace SchubertGeometry

private theorem model_projective {I : Type u}
    {S R K : Type u} [CommRing S] [CommRing R] [CommRing K]
    [Algebra S R] [Algebra R K]
    (P : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (he : ∀ s t (f : s ⟶ t), (e t).toAlgHom.comp
        (Algebra.TensorProduct.lTensor (S := K) K (N.map f).hom) =
      (F.map f).hom.comp (e s).toAlgHom)
    (hi : ∀ s, Function.Injective (fun x : N.obj s ↦ e s ((1 : K) ⊗ₜ[R] x)))
    (q : fixedFibreDiagram (R := R) (M := R) P ≅ N)
    (v : ∀ s, P.obj s →+* F.obj s)
    (hq : ∀ s x, e s ((1 : K) ⊗ₜ[R] (q.hom.app s).hom ((1 : R) ⊗ₜ[S] x)) = v s x)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j : I // j ∈ s.val})
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), F.obj s)
    (hm : ∀ s j hj k hk,
      (c s j hj k hk : F.obj s) ∈ Set.range (v s) ∧
      (↑((c s j hj k hk)⁻¹) : F.obj s) ∈ Set.range (v s) ∧
      a s j hj k hk ∈ Set.range (v s))
    (hco : ∀ s j hj k hk l hl,
      c s j hj l hl = c s k hk l hl * c s j hj k hk ∧
      a s j hj l hl = (c s k hk l hl : F.obj s) * a s j hj k hk + a s k hk l hl)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toRingHom.toMonoidHom (c s j hj k hk) =
        c t j ((leOfHom f) hj) k ((leOfHom f) hk) ∧
      (F.map f).hom (a s j hj k hk) =
        a t j ((leOfHom f) hj) k ((leOfHom f) hk)) :
    modelProjectiveSpec N F e sel c a := by
  obtain ⟨c₀, a₀, hc₀, ha₀, hco₀, hn₀⟩ :=
    retained_transition_lifts P N F e he hi q v hq c a hm hco hn
  exact ⟨c₀, a₀, hc₀, ha₀, hco₀, hn₀,
    exists_projective_transition N sel c₀ a₀ hco₀ hn₀⟩

end SchubertGeometry
