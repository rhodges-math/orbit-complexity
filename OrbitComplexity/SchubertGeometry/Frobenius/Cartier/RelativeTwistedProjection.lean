import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedNormalization
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The original positive polynomial after insertion at infinity -/

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

open private infinity_fst
  from OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.InfinityFactor

private theorem value_congr {X : Scheme.{u}} {M N : X.Modules}
    (f g : M ⟶ N) (h : f = g) (U : X.Opens) (s : M.val.obj (op U)) :
    (f.val.app (op U)).hom s = (g.val.app (op U)).hom s := by
  cases h
  rfl

private theorem firstProjection {A : Type u} [CommRing A] {p : ℕ}
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) :
    m ≫ ProjectiveLine.projectiveInfinityFactor A (p - 1) ≫
        projectiveCartierProjection A p (⟨0⟩ : indices.{u}) =
      m ≫ pullback.fst (ProjectiveLine.leftRestriction A)
        (ProjectiveLine.twistedRestriction A (p - 1)) := by
  change m ≫ ProjectiveLine.projectiveInfinityFactor A (p - 1) ≫
      pullback.fst (ProjectiveLine.leftRestriction A)
        (ProjectiveLine.twistedRestriction A (2 * (p - 1))) = _
  rw [infinity_fst]

/-- Inserting the infinity factor preserves the original positive polynomial of
a projective section. -/
theorem insertedInfinity_left {A : Type u} [CommRing A] {p : ℕ}
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) :
    sectionWeight (p := p) (insertedInfinity m) (⟨0⟩ : indices.{u}) =
      (Scheme.ΓSpecIso (.of (Polynomial A))).hom
        (((m ≫ pullback.fst (ProjectiveLine.leftRestriction A)
          (ProjectiveLine.twistedRestriction A (p - 1))).val.app (op ⊤)).hom
            (1 : Γ(line A, ⊤))) := by
  have h := value_congr _ _ (firstProjection m) ⊤ (1 : Γ(line A, ⊤))
  exact (insertedInfinity_coefficient m (⟨0⟩ : indices.{u})).trans
    (congrArg (Scheme.ΓSpecIso (.of (Polynomial A))).hom h)


end SchubertGeometry.ProjectiveCartier
