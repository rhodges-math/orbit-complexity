import Mathlib.AlgebraicGeometry.AffineScheme
import Batteries.Tactic.Lint

/-! # Pointed isomorphisms between affine open images

Two open embeddings of one affine scheme identify their images. A section of
the common scheme gives a section of either image, with its projection retained.
-/

open AlgebraicGeometry CategoryTheory

namespace FrobeniusSplitting

universe u

private noncomputable def open_image_over_iso {B : Scheme.{u}} {W X : Over B}
    (c : W ⟶ X) [IsOpenImmersion c.left] :
    W ≅ Over.mk (c.left.opensRange.ι ≫ X.hom) :=
  Over.isoMk c.left.isoOpensRange (by
    change c.left.isoOpensRange.hom ≫ (c.left.opensRange.ι ≫ X.hom) = W.hom
    rw [← Category.assoc, c.left.isoOpensRange_hom_ι, Over.w c])

/-- Two open embeddings of a pointed affine scheme give a pointed isomorphism
of affine opens, retaining the endpoint triangle and the section's projection. -/
theorem exists_pointed_open_iso {B : Scheme.{u}}
    (W C F : Over B) [IsAffine W.left]
    (c : W ⟶ C) (j : W ⟶ F)
    [IsOpenImmersion c.left] [IsOpenImmersion j.left]
    (e : C ⟶ F) (h : c ≫ e = j)
    (k : B ⟶ W.left) (hk : k ≫ W.hom = 𝟙 B) :
    ∃ (U : C.left.Opens) (V : F.left.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧
      ∃ E : Over.mk (U.ι ≫ C.hom) ≅ Over.mk (V.ι ≫ F.hom),
        E.hom.left ≫ V.ι = U.ι ≫ e.left ∧
        ∃ s : B ⟶ V.toScheme,
          s ≫ (V.ι ≫ F.hom) = 𝟙 B ∧ s ≫ V.ι = k ≫ j.left := by
  let U := c.left.opensRange
  let V := j.left.opensRange
  let a := c.left.isoOpensRange
  let b := j.left.isoOpensRange
  let EC := open_image_over_iso c
  let EJ := open_image_over_iso j
  let E : Over.mk (U.ι ≫ C.hom) ≅ Over.mk (V.ι ≫ F.hom) := EC.symm ≪≫ EJ
  have he : c.left ≫ e.left = j.left := congrArg Over.Hom.left h
  have hE : E.hom.left ≫ V.ι = U.ι ≫ e.left := by
    change (a.inv ≫ b.hom) ≫ V.ι = U.ι ≫ e.left
    rw [Category.assoc, j.left.isoOpensRange_hom_ι, ← he,
      ← Category.assoc, c.left.isoOpensRange_inv_comp]
  let s : B ⟶ V.toScheme := k ≫ b.hom
  have hs : s ≫ V.ι = k ≫ j.left := by
    change (k ≫ b.hom) ≫ V.ι = k ≫ j.left
    rw [Category.assoc, j.left.isoOpensRange_hom_ι]
  refine ⟨U, V, isAffineOpen_opensRange c.left, isAffineOpen_opensRange j.left,
    E, hE, s, ?_, hs⟩
  rw [← Category.assoc, hs, Category.assoc, Over.w j, hk]

end FrobeniusSplitting
