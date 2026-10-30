import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Projective spaces over a commutative ring

The total polynomial grading constructs projective space as a scheme. Constants identify its
degree-zero base with the original ring, and finitely many variables give a proper structure map.
-/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GroupActions
variable (R ι : Type u) [CommRing R]

private def constants : R →+* MvPolynomial.homogeneousSubmodule ι R 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ _⟩
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_add' x y := Subtype.ext (map_add MvPolynomial.C x y)
  map_mul' x y := Subtype.ext (map_mul MvPolynomial.C x y)

private theorem constants_bijective : Function.Bijective (constants R ι) := by
  constructor
  · intro x y h
    exact (MvPolynomial.C_injective ι R) (congrArg Subtype.val h)
  · intro p
    refine ⟨p.val.coeff 0, Subtype.ext ?_⟩
    have h := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (p := p.val)).mpr p.property
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h).symm

/-- The degree-zero homogeneous polynomials are the constants. -/
def projectiveZeroIso : R ≃+* MvPolynomial.homogeneousSubmodule ι R 0 :=
  RingEquiv.ofBijective (constants R ι) (constants_bijective R ι)

/-- Projective space is the projective spectrum of the polynomial ring's total grading. -/
abbrev projectiveScheme : Scheme := Proj (MvPolynomial.homogeneousSubmodule ι R)

/-- The structure morphism from projective space to the spectrum of the coefficient ring. -/
def projectiveToSpec :
    projectiveScheme R ι ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι R) ≫
    Spec.map (projectiveZeroIso R ι).toCommRingCatIso.hom

variable [Finite ι]

/-- Projective space with finitely many homogeneous coordinates is proper over its base. -/
instance projectiveToSpec_isProper : IsProper (projectiveToSpec R ι) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule ι R 0)
      (MvPolynomial ι R) := by
    refine ⟨⟨Finset.univ.image (MvPolynomial.X : ι → MvPolynomial ι R), ?_⟩⟩
    apply eq_top_iff.mpr
    intro p hp_top
    clear hp_top
    induction p using MvPolynomial.induction_on with
    | C r =>
      exact Subalgebra.algebraMap_mem _ (constants R ι r)
    | add p q hp hq => exact Subalgebra.add_mem _ hp hq
    | mul_X p j hp =>
      exact Subalgebra.mul_mem _ hp
        (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨j, Finset.mem_univ j, rfl⟩)))
  unfold projectiveToSpec
  infer_instance

end GroupActions
