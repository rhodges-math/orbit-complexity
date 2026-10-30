import OrbitComplexity.SchubertGeometry.Frobenius.BorelSectionCharacter
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Function

/-! # character coefficients of the same retained arithmetic units -/

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups Opposite
open scoped CategoryTheory.MonObj
noncomputable section
universe u
namespace SchubertGeometry.RetainedCharacter

private theorem affineSection_pull {A B : CommRingCat.{u}} (f : Spec A ⟶ Spec B) (x : B) :
    f.appTop ((Scheme.ΓSpecIso B).inv x) =
      (Scheme.ΓSpecIso A).inv ((Spec.preimage f).hom x) := by
  have h := congrArg (fun q : B ⟶ Γ(Spec A, ⊤) ↦ q x)
    (Scheme.ΓSpecIso_inv_naturality (Spec.preimage f))
  simpa only [Spec.map_preimage, CommRingCat.comp_apply] using h.symm

private theorem coefficientSection_map {A B : CommRingCat.{u}} (f : A ⟶ B) (x : A) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso A).inv x) = (Scheme.ΓSpecIso B).inv (f.hom x) := by
  exact (congrArg (fun q : A ⟶ Γ(Spec B, ⊤) ↦ q x)
    (Scheme.ΓSpecIso_inv_naturality f)).symm

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem section_character_power (A : CommAlgCat K)
    (b : (algSpec (.of K)).obj (.op A) ⟶ (borelVariety G).toOver) (n : ℕ) :
    b.left.appTop (CharacterLine.borelCharacterSection G (G.positiveRootCharacter ^ n)) =
      (Scheme.ΓSpecIso (.of A)).inv ((ProjectiveLine.positiveBorelSection G A b : A) ^ n) := by
  let t : G.borelAlgebra →ₐ[K] A :=
    ((Spec.mapMulEquiv (R := K) (S := G.borelAlgebra) (T := A)).symm b).ofConv
  obtain ⟨z, _, hz⟩ := borelCharacterMap_points G t
  let x : MonoidAlgebra K (Multiplicative ℤ) :=
    MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : K)
  have hzpow : t (borelCharacterMap G (G.positiveRootCharacter ^ n) x) =
      z (MonoidAlgebra.single (G.positiveRootCharacter ^ n) 1) := hz _
  have hzone : t (borelCharacterMap G G.positiveRootCharacter x) =
      z (MonoidAlgebra.single G.positiveRootCharacter 1) := hz _
  have hp : t (borelCharacterMap G (G.positiveRootCharacter ^ n) x) =
      (t (borelCharacterMap G G.positiveRootCharacter x)) ^ n := by
    calc
      _ = z (MonoidAlgebra.single (G.positiveRootCharacter ^ n) 1) := hzpow
      _ = z ((MonoidAlgebra.single G.positiveRootCharacter 1) ^ n) := by
        rw [MonoidAlgebra.single_pow, one_pow]
      _ = (z (MonoidAlgebra.single G.positiveRootCharacter 1)) ^ n := map_pow z _ n
      _ = _ := congrArg (fun a : A ↦ a ^ n) hzone.symm
  have hp' : (Spec.preimage b.left).hom
      (borelCharacterMap G (G.positiveRootCharacter ^ n) x) =
        (ProjectiveLine.positiveBorelSection G A b : A) ^ n :=
    hp.trans (congrArg (fun a : A ↦ a ^ n) (ProjectiveLine.positiveBorelSection_val G A b).symm)
  change b.left.appTop ((Scheme.ΓSpecIso (.of G.borelAlgebra)).inv
      (borelCharacterMap G (G.positiveRootCharacter ^ n) x)) = _
  exact (affineSection_pull b.left _).trans
    (congrArg (Scheme.ΓSpecIso (.of A)).inv hp')

end SchubertGeometry.RetainedCharacter

