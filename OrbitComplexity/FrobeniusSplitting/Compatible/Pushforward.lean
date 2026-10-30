import OrbitComplexity.FrobeniusSplitting.Compatible.Schemes
import OrbitComplexity.FrobeniusSplitting.Splittings.Pushforward
import Batteries.Tactic.Lint

/-! # Compatible ideals under pushforward

Compatibility with the kernel of a quasi-compact morphism holds on every open
set. Consequently pushforward of a splitting preserves the kernel of the
composite morphism, without hypotheses on the image scheme.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace FrobeniusSplitting.SchemeSplitting

universe u

private theorem app_restrict {X Z : Scheme.{u}} (i : Z ⟶ X)
    {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    Z.presheaf.map (homOfLE (i.preimage_mono h)).op (i.app U a) =
      i.app V (X.presheaf.map (homOfLE h).op a) := by
  exact (congrArg (fun t : Γ(X, U) ⟶ Γ(Z, i ⁻¹ᵁ V) => t a)
    (i.naturality (homOfLE h).op)).symm

/-- Compatibility with a morphism kernel preserves its vanishing sections on
all opens, including opens which are not affine. -/
theorem IsCompatible.ker_onOpen {X Z : Scheme.{u}} {p : ℕ}
    {splitting : SchemeSplitting X p} {i : Z ⟶ X} [QuasiCompact i]
    (hi : splitting.IsCompatible i.ker) (U : X.Opens) (a : Γ(X, U))
    (ha : i.app U a = 0) : i.app U (splitting.onOpen U a) = 0 := by
  apply Z.IsSheaf.section_ext
  intro z hz
  obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show i z ∈ U from hz)
  have hle : V ≤ U := hVU
  let rX := X.presheaf.map (homOfLE hle).op
  let rZ := Z.presheaf.map (homOfLE (i.preimage_mono hle)).op
  have hzA : i.app V (rX a) = 0 :=
    (app_restrict i hle a).symm.trans ((congrArg rZ ha).trans rZ.hom.map_zero)
  have hm : rX a ∈ i.ker.ideal ⟨V, hV⟩ := by
    rw [Scheme.Hom.ker_apply]
    exact hzA
  have hs : i.app V (splitting.onOpen V (rX a)) = 0 := by
    have hs := hi ⟨V, hV⟩ hm
    rw [Scheme.Hom.ker_apply] at hs
    exact hs
  refine ⟨i ⁻¹ᵁ V, i.preimage_mono hle, hzV, ?_⟩
  calc
    rZ (i.app U (splitting.onOpen U a)) =
        i.app V (rX (splitting.onOpen U a)) := app_restrict i hle _
    _ = i.app V (splitting.onOpen V (rX a)) :=
      congrArg (i.app V) (splitting.restrict_comm hle a).symm
    _ = 0 := hs
    _ = rZ 0 := rZ.hom.map_zero.symm

/-- Pushforward of a splitting preserving a morphism kernel preserves the
kernel of the composite morphism. -/
theorem IsCompatible.pushforward_ker {X Y Z : Scheme.{u}} {p : ℕ}
    (splitting : SchemeSplitting X p) (i : Z ⟶ X) [QuasiCompact i]
    (f : X ⟶ Y) [QuasiCompact f] [IsIso f.c]
    (hi : splitting.IsCompatible i.ker) :
    (splitting.pushforward f).IsCompatible (i ≫ f).ker := by
  intro U a ha
  rw [Scheme.Hom.ker_apply] at ha ⊢
  have hzero : i.app (f ⁻¹ᵁ U) (f.app U a) = 0 := by
    change i.app (f ⁻¹ᵁ U) (f.app U a) = 0 at ha
    exact ha
  have hs := hi.ker_onOpen (f ⁻¹ᵁ U) (f.app U a) hzero
  change i.app (f ⁻¹ᵁ U) (f.app U ((splitting.pushforward f).onOpen U a)) = 0
  exact (congrArg (fun s : Γ(X, f ⁻¹ᵁ U) => i.app (f ⁻¹ᵁ U) s)
    (pushforward_app splitting f U a)).trans hs

end FrobeniusSplitting.SchemeSplitting
