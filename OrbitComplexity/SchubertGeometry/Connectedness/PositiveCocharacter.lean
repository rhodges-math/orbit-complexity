import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.PositiveCoroots
import OrbitComplexity.GroupActions.Tori.Coordinates
import OrbitComplexity.GroupActions.Varieties.TorusVariety
import Mathlib.Algebra.Polynomial.Laurent

/-!
# The positive cocharacter of the original maximal torus

The full integral character functional defines a regular map from the
multiplicative group to the chosen maximal torus. Every root character pulls
back to the Laurent monomial with exponent twice its original-base height.

-/

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions

noncomputable section

namespace SchubertGeometry.CellContraction

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

universe u

section Generic

variable {K A B C : Type u} [CommRing K] [CommRing A] [CommRing B] [CommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C]

private theorem spec_comp_of_eq
    (q : A →+* B) (f : B →+* C) (g : A →+* C) (h : f.comp q = g) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom q) =
      Spec.map (CommRingCat.ofHom g) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

private theorem spec_algebra_over (f : A →ₐ[K] B) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K B)) :=
  spec_comp_of_eq (algebraMap K A) f.toRingHom (algebraMap K B)
    (RingHom.ext f.commutes)

private def specAlgebraHom (f : A →ₐ[K] B) :
    (Spec (.of B)).asOver (Spec (.of K)) ⟶
      (Spec (.of A)).asOver (Spec (.of K)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (spec_algebra_over f)

variable {M : Type u} [CommMonoid M]

private def laurentFromMultiplicative :
    MonoidAlgebra K (Multiplicative ℤ) ≃ₐ[K] LaurentPolynomial K :=
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv K K ℤ).symm

private theorem laurentFromMultiplicative_single (m : Multiplicative ℤ) :
    laurentFromMultiplicative (MonoidAlgebra.single m (1 : K)) =
      LaurentPolynomial.T m.toAdd := by
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv K K ℤ).injective
  rw [show laurentFromMultiplicative (MonoidAlgebra.single m (1 : K)) =
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv K K ℤ).symm
      (MonoidAlgebra.single m 1) from rfl, AlgEquiv.apply_symm_apply]
  exact (AddMonoidAlgebra.toMultiplicativeAlgEquiv_single
    (R := K) (A := K) (M := ℤ) m.toAdd 1).symm

private def torusAlgebraAlong
    (e : A ≃ₐ[K] MonoidAlgebra K M) (d : M →* Multiplicative ℤ) :
    A →ₐ[K] LaurentPolynomial K :=
  (laurentFromMultiplicative.toAlgHom.comp
    (MonoidAlgebra.mapDomainBialgHom K d).toAlgHom).comp e.toAlgHom

private theorem torusAlgebraAlong_single
    (e : A ≃ₐ[K] MonoidAlgebra K M) (d : M →* Multiplicative ℤ)
    (m : M) (n : ℤ) (hn : (d m).toAdd = n) :
    torusAlgebraAlong e d (e.symm (MonoidAlgebra.single m 1)) =
      LaurentPolynomial.T n := by
  change laurentFromMultiplicative ((MonoidAlgebra.mapDomainBialgHom K d)
    (e (e.symm (MonoidAlgebra.single m 1)))) = _
  rw [AlgEquiv.apply_symm_apply, MonoidAlgebra.mapDomainBialgHom_single,
    laurentFromMultiplicative_single, hn]

private theorem torusAlgebraAlong_factor [CoalgebraStruct K B]
    (e : A ≃ₐ[K] MonoidAlgebra K M) (d : M →* Multiplicative ℤ)
    (q : B →+* A) (p : B →ₐc[K] MonoidAlgebra K M)
    (he : e.toAlgHom.toRingHom.comp q = p.toAlgHom.toRingHom) :
    (torusAlgebraAlong e d).toRingHom.comp q =
      laurentFromMultiplicative.toAlgHom.toRingHom.comp
        ((MonoidAlgebra.mapDomainBialgHom K d).comp p).toAlgHom.toRingHom := by
  apply RingHom.ext
  intro b
  change laurentFromMultiplicative ((MonoidAlgebra.mapDomainBialgHom K d) (e (q b))) =
    laurentFromMultiplicative ((MonoidAlgebra.mapDomainBialgHom K d) (p b))
  exact congrArg (fun x => laurentFromMultiplicative
    ((MonoidAlgebra.mapDomainBialgHom K d) x))
    (RingHom.congr_fun he b)

end Generic

section Native

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def cocharacterLaurentMap : G.coordinateAlgebra →ₐ[K] LaurentPolynomial K :=
  laurentFromMultiplicative.toAlgHom.comp (positiveCocharacterMap G).toAlgHom

/-- The original torus coordinate map of the positive-coroot cocharacter. -/
def positiveTorusAlgebra : G.torusAlgebra →ₐ[K] LaurentPolynomial K :=
  torusAlgebraAlong (torusCoordinateEquiv G) (positiveCocharacter G)

/-- Every original torus character evaluates as the Laurent monomial of its
integral positive-cocharacter exponent. -/
theorem positiveTorusAlgebra_character (chi : G.characters) :
    positiveTorusAlgebra G
      ((torusCoordinateEquiv G).symm (MonoidAlgebra.single chi 1)) =
        LaurentPolynomial.T ((positiveCocharacter G chi).toAdd) :=
  torusAlgebraAlong_single (torusCoordinateEquiv G) (positiveCocharacter G)
    chi ((positiveCocharacter G chi).toAdd) rfl

/-- Every original root character evaluates along the cocharacter as its
Laurent monomial of twice the original-base height. -/
theorem positiveTorusAlgebra_root (r : G.rootIndex) :
    positiveTorusAlgebra G
      ((torusCoordinateEquiv G).symm (MonoidAlgebra.single (G.rootCharacter r) 1)) =
        LaurentPolynomial.T (2 * G.rootBase.height r) := by
  rw [positiveTorusAlgebra_character, positiveCocharacter_root]

/-- The original torus coordinate map factors the original full-character
cocharacter through the same coordinate quotient as the torus inclusion. -/
theorem positiveTorusAlgebra_factor :
    (positiveTorusAlgebra G).toRingHom.comp
        (Ideal.Quotient.mk G.torusIdeal.toIdeal) =
      (cocharacterLaurentMap G).toRingHom :=
  torusAlgebraAlong_factor (torusCoordinateEquiv G) (positiveCocharacter G)
    (Ideal.Quotient.mk G.torusIdeal.toIdeal) G.torusSplit
    (RingHom.ext (torusCoordinateEquiv_mk G))

/-- The specified regular positive-cocharacter map from the multiplicative
group to the chosen maximal torus, over the original coefficient field. -/
def positiveTorusCocharacter :
    (Spec (.of (LaurentPolynomial K))).asOver (Spec (.of K)) ⟶
      (torusVariety G).toOver :=
  specAlgebraHom (positiveTorusAlgebra G)

/-- The positive torus cocharacter has the original spectrum map as its
underlying scheme morphism. -/
theorem positiveTorusCocharacter_left :
    (positiveTorusCocharacter G).left =
      Spec.map (CommRingCat.ofHom (positiveTorusAlgebra G).toRingHom) := rfl

/-- Composing the original torus cocharacter with the original torus inclusion
recovers the original positive-cocharacter bialgebra map. -/
theorem positiveTorusCocharacter_comp :
    (positiveTorusCocharacter G).left ≫ (torusInclusion G).left =
      Spec.map (CommRingCat.ofHom (cocharacterLaurentMap G).toRingHom) := by
  rw [positiveTorusCocharacter_left, torusInclusion_left]
  exact spec_comp_of_eq (Ideal.Quotient.mk G.torusIdeal.toIdeal)
    (positiveTorusAlgebra G).toRingHom (cocharacterLaurentMap G).toRingHom
    (positiveTorusAlgebra_factor G)

end Native

end SchubertGeometry.CellContraction
