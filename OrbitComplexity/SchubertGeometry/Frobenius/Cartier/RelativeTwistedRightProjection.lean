import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedProjection
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedCoefficients
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The infinity factor in the negative polynomial chart -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting

noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

open private indices line sourceLine unitLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

open private insertedInfinity sectionPolynomial insertedInfinity_coefficient
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections

open private sectionWeight
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator

open private infinity_snd chart1Multiply
  from OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.InfinityFactor

open private chart1Multiply_top
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedCoefficients

open private module_comp_apply
  from OrbitComplexity.SchubertGeometry.LineBundles.Affine.GlobalAffineEndpoint

open private value_congr
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedProjection

private theorem equiv_weight {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (r : S) (a : R) :
    e (e.symm r * a) = e a * r := by
  rw [map_mul, e.apply_symm_apply]
  exact mul_comm _ _

private theorem rightProjection {A : Type u} [CommRing A] {p : ℕ}
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) :
    m ≫ ProjectiveLine.projectiveInfinityFactor A (p - 1) ≫
        projectiveCartierProjection A p (⟨1⟩ : indices.{u}) =
      (m ≫ pullback.snd (ProjectiveLine.leftRestriction A)
        (ProjectiveLine.twistedRestriction A (p - 1))) ≫ chart1Multiply A (p - 1) := by
  change m ≫ ProjectiveLine.projectiveInfinityFactor A (p - 1) ≫
      pullback.snd (ProjectiveLine.leftRestriction A)
        (ProjectiveLine.twistedRestriction A (2 * (p - 1))) = _
  exact (congrArg (fun f => m ≫ f) (infinity_snd A (p - 1))).trans
    (Category.assoc m _ _).symm

/-- In the negative chart, insertion at infinity multiplies the original
polynomial by X to the power p-1. -/
theorem insertedInfinity_right {A : Type u} [CommRing A] {p : ℕ}
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) :
    sectionWeight (p := p) (insertedInfinity m) (⟨1⟩ : indices.{u}) =
      (Scheme.ΓSpecIso (.of (Polynomial A))).hom
        (((m ≫ pullback.snd (ProjectiveLine.leftRestriction A)
          (ProjectiveLine.twistedRestriction A (p - 1))).val.app (op ⊤)).hom
            (1 : Γ(line A, ⊤))) * Polynomial.X ^ (p - 1) := by
  let f := m ≫ pullback.snd (ProjectiveLine.leftRestriction A)
    (ProjectiveLine.twistedRestriction A (p - 1))
  let a : Γ(Spec (.of (Polynomial A)), ⊤) :=
    (f.val.app (op ⊤)).hom (1 : Γ(line A, ⊤))
  have h := value_congr _ _ (rightProjection m) ⊤ (1 : Γ(line A, ⊤))
  have hv := module_comp_apply f (chart1Multiply A (p - 1)) ⊤ (1 : Γ(line A, ⊤))
  have ha := chart1Multiply_top A (p - 1) a
  have hp : sectionPolynomial m (⟨1⟩ : indices.{u}) =
      (Scheme.ΓSpecIso (.of (Polynomial A))).hom
        ((Scheme.ΓSpecIso (.of (Polynomial A))).inv (Polynomial.X ^ (p - 1)) * a) :=
    congrArg (Scheme.ΓSpecIso (.of (Polynomial A))).hom ((h.trans hv).trans ha)
  refine (insertedInfinity_coefficient m (⟨1⟩ : indices.{u})).trans (hp.trans ?_)
  let e := (Scheme.ΓSpecIso (.of (Polynomial A))).commRingCatIsoToRingEquiv
  exact equiv_weight e (Polynomial.X ^ (p - 1)) a


end SchubertGeometry.ProjectiveCartier
