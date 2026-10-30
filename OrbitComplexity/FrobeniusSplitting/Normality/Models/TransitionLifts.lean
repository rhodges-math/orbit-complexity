import OrbitComplexity.FrobeniusSplitting.Normality.Models.TransitionLiftsData

/-! # Affine parameters in a specified coordinate diagram -/

open CategoryTheory
noncomputable section
universe u v
namespace FrobeniusSplitting

private theorem unit_of_range {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hi : Function.Injective f) (c : Bˣ)
    (hc : (c : B) ∈ Set.range f) (hinv : (↑(c⁻¹) : B) ∈ Set.range f) :
    ∃ d : Aˣ, f (d : A) = c := by
  obtain ⟨x, hx⟩ := hc
  obtain ⟨y, hy⟩ := hinv
  have hxy : x * y = 1 := by
    apply hi
    rw [map_mul, hx, hy, map_one]
    exact c.mul_inv
  exact ⟨Units.mkOfMulEqOne x y hxy, hx⟩

/-- Retained values and inverses give units with every original cocycle and restriction. -/
theorem exists_transition_lifts {I : Type v} {R K : Type u} [CommRing R] [CommRing K]
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (e : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (hi : ∀ s, Function.Injective (e.app s).hom)
    (c : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), (F.obj s)ˣ)
    (a : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val)
      (k : I) (_ : k ∈ s.val), F.obj s)
    (hm : ∀ s j hj k hk,
      (c s j hj k hk : F.obj s) ∈ Set.range (e.app s).hom ∧
      (↑((c s j hj k hk)⁻¹) : F.obj s) ∈ Set.range (e.app s).hom ∧
      a s j hj k hk ∈ Set.range (e.app s).hom)
    (hco : ∀ s j hj k hk l hl,
      c s j hj l hl = c s k hk l hl * c s j hj k hk ∧
      a s j hj l hl = (c s k hk l hl : F.obj s) * a s j hj k hk + a s k hk l hl)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toRingHom.toMonoidHom (c s j hj k hk) =
        c t j ((leOfHom f) hj) k ((leOfHom f) hk) ∧
      (F.map f).hom (a s j hj k hk) =
        a t j ((leOfHom f) hj) k ((leOfHom f) hk)) :
    transitionLiftSpec N F e c a := by
  classical
  have hc : ∀ s j hj k hk, ∃ d : (N.obj s)ˣ,
      (e.app s).hom (d : N.obj s) = (c s j hj k hk : F.obj s) := by
    intro s j hj k hk
    exact unit_of_range (e.app s).hom (hi s) (c s j hj k hk)
      (hm s j hj k hk).1 (hm s j hj k hk).2.1
  choose c₀ hc using hc
  have ha : ∀ s j hj k hk, ∃ x : N.obj s,
      (e.app s).hom x = a s j hj k hk := by
    intro s j hj k hk
    exact (hm s j hj k hk).2.2
  choose a₀ ha using ha
  have he (s t) (f : s ⟶ t) (x : N.obj s) :
      (e.app t).hom ((N.map f).hom x) = (F.map f).hom ((e.app s).hom x) := by
    exact congrArg (fun q ↦ q.hom x) (e.naturality f)
  refine ⟨c₀, a₀, hc, ha, ?_, ?_⟩
  · intro s j hj k hk l hl
    constructor
    · apply Units.ext
      apply hi s
      change (e.app s).hom (c₀ s j hj l hl : N.obj s) =
        (e.app s).hom ((c₀ s k hk l hl : N.obj s) * (c₀ s j hj k hk : N.obj s))
      rw [map_mul, hc, hc, hc]
      exact congrArg Units.val (hco s j hj k hk l hl).1
    · apply hi s
      rw [map_add, map_mul, ha, hc, ha, ha]
      exact (hco s j hj k hk l hl).2
  · intro s t f j hj k hk
    constructor
    · apply Units.ext
      apply hi t
      change (e.app t).hom ((N.map f).hom (c₀ s j hj k hk : N.obj s)) =
        (e.app t).hom (c₀ t j ((leOfHom f) hj) k ((leOfHom f) hk) : N.obj t)
      rw [he, hc, hc]
      exact congrArg Units.val (hn s t f j hj k hk).1
    · apply hi t
      rw [he, ha, ha]
      exact (hn s t f j hj k hk).2

end FrobeniusSplitting
