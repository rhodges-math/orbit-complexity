import OrbitComplexity.FrobeniusSplitting.Splittings.Localization
import OrbitComplexity.FrobeniusSplitting.Splittings.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Batteries.Tactic.Lint

/-! # Uniqueness of splittings on affine schemes

Restriction to a basic open is the unique localization of the splitting on
global sections. The sheaf condition then determines the splitting on every
open subset from its value on global sections.
-/

open AlgebraicGeometry CategoryTheory Opposite

namespace FrobeniusSplitting.SchemeSplitting

universe u

private theorem basic_eq {X : Scheme.{u}} [IsAffine X] {p : ℕ}
    (source target : SchemeSplitting X p) (hp : 0 < p)
    (h : source.onOpen ⊤ = target.onOpen ⊤) (f : Γ(X, ⊤)) :
    source.onOpen (X.basicOpen f) = target.onOpen (X.basicOpen f) := by
  have hs := RingSplitting.localize_eq (S := Γ(X, X.basicOpen f)) (Submonoid.powers f)
    (source.onOpen ⊤) hp (source.onOpen (X.basicOpen f))
    (fun a => source.restrict_comm le_top a)
  have ht := RingSplitting.localize_eq (S := Γ(X, X.basicOpen f)) (Submonoid.powers f)
    (target.onOpen ⊤) hp (target.onOpen (X.basicOpen f))
    (fun a => target.restrict_comm le_top a)
  exact hs.symm.trans ((congrArg (fun t : RingSplitting Γ(X, ⊤) p =>
    RingSplitting.localize (S := Γ(X, X.basicOpen f)) (Submonoid.powers f) t hp) h).trans ht)

/-- A splitting on an affine scheme is determined by its action on global sections. -/
theorem eq_of_top {X : Scheme.{u}} [IsAffine X] {p : ℕ}
    (source target : SchemeSplitting X p) (hp : 0 < p)
    (h : source.onOpen ⊤ = target.onOpen ⊤) : source = target := by
  apply SchemeSplitting.ext
  intro U s
  apply X.IsSheaf.section_ext
  intro x hx
  obtain ⟨f, hf, hxf⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x, hx⟩ (by trivial)
  refine ⟨X.basicOpen f, hf, hxf, ?_⟩
  exact (source.restrict_comm hf s).symm.trans
    ((congrArg (fun t : RingSplitting Γ(X, X.basicOpen f) p =>
      t (X.presheaf.map (homOfLE hf).op s)) (basic_eq source target hp h f)).trans
        (target.restrict_comm hf s))

end FrobeniusSplitting.SchemeSplitting
