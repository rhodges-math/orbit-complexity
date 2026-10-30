import OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterLine
import OrbitComplexity.ReductiveGroups.Roots.Characters.PositiveCharacter

/-! # The full positive-root character on affine Borel sections

These are regular sections over arbitrary coefficient algebras, not rational
points. The character is independent of a residue prime. Its multiplication
and inverse laws are those of the Borel group object.
-/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open AlgebraicGeometry CategoryTheory GroupActions ReductiveGroups Opposite
open scoped CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The full positive-root character evaluated on an affine Borel section. -/
def positiveBorelSection (A : CommAlgCat K) :
    ((algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) →* Aˣ := by
  change ((Spec (.of A)).asOver (Spec (.of K)) ⟶
    (Spec (.of G.borelAlgebra)).asOver (Spec (.of K))) →* Aˣ
  exact (borelCharacterUnit G G.positiveRootCharacter).comp
    (Spec.mapMulEquiv (R := K) (S := G.borelAlgebra) (T := A)).symm.toMonoidHom

/-- The section character is the value of its Hopf coordinate generator. -/
theorem positiveBorelSection_val (A : CommAlgCat K)
    (b : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    (positiveBorelSection G A b : A) =
      (Spec.preimage b.left).hom
        (borelCharacterMap G G.positiveRootCharacter
          (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) := rfl

private theorem preimage_naturality {R S T : CommRingCat} (f : R ⟶ S)
    (b : Spec R ⟶ Spec T) (x : T) :
    (Spec.preimage (Spec.map f ≫ b)).hom x = f.hom ((Spec.preimage b).hom x) := by
  rw [Spec.preimage_comp, Spec.preimage_map]
  rfl

/-- Pulling back the Borel section applies the same coefficient map to
its full character, including every central character factor. -/
theorem positiveBorelSection_natural {A D : CommAlgCat K} (f : A ⟶ D)
    (b : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) :
    positiveBorelSection G D ((algSpec (.of K)).map f.op ≫ b) =
      Units.map f.hom.toMonoidHom (positiveBorelSection G A b) := by
  apply Units.ext
  rw [positiveBorelSection_val, Units.coe_map, positiveBorelSection_val]
  exact preimage_naturality (CommRingCat.ofHom f.hom.toRingHom)
    (show Spec (.of A) ⟶ Spec (.of G.borelAlgebra) from b.left) _

end SchubertGeometry.ProjectiveLine
