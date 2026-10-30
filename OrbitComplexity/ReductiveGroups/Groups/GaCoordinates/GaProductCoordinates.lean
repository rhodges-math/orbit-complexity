import OrbitComplexity.ReductiveGroups.Groups.Generated.GaGeneratedSubgroup
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Ga Product Coordinates

Ordered products of additive subgroups define polynomial maps
into their generated closed subgroup. Products retain their order. -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv

universe u v
variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]
  {ι : Type v}

/-- The point of an additive subgroup at an arbitrary parameter
in a commutative value algebra. -/
def gaParameterPoint (x : B →ₐc[K] SymmetricAlgebra K K)
    {A : Type*} [CommRing A] [Algebra K A] (a : A) : WithConv (B →ₐ[K] A) :=
  AlgHom.mapDomain x
    ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := A)).symm (Multiplicative.ofAdd a))

/-- The equality is

```lean
AlgHom.mapValue φ (gaParameterPoint x a) = gaParameterPoint x (φ a)
```
-/
theorem gaParameterPoint_mapValue
    (x : B →ₐc[K] SymmetricAlgebra K K)
    {A A' : Type*} [CommRing A] [Algebra K A] [CommRing A'] [Algebra K A']
    (φ : A →ₐ[K] A') (a : A) :
    AlgHom.mapValue φ (gaParameterPoint x a) = gaParameterPoint x (φ a) := by
  unfold gaParameterPoint
  have h := DFunLike.congr_fun (AlgHom.mapValue_mapDomain x φ)
    ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := A)).symm (Multiplicative.ofAdd a))
  simp only [MonoidHom.comp_apply] at h
  rw [← h, AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply]
  rfl

/-- The equality is

```lean
gaParameterPoint x (0 : A) = 1
```
-/
@[simp] theorem gaParameterPoint_zero
    (x : B →ₐc[K] SymmetricAlgebra K K)
    {A : Type*} [CommRing A] [Algebra K A] : gaParameterPoint x (0 : A) = 1 := by
  change AlgHom.mapDomain x
    ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := A)).symm 1) = 1
  rw [map_one, map_one]

/-- The coordinate pullback of the ordered Ga product. This is an
algebra map, not a Hopf map: the factors need not commute. -/
def gaProductCoordinate (x : ι → B →ₐc[K] SymmetricAlgebra K K) (l : List ι) :
    B →ₐ[K] MvPolynomial ι K :=
  ((l.map (fun i => gaParameterPoint (x i) (MvPolynomial.X i))).prod).ofConv

/-- Specializing the universal coordinates gives the ordered product of
the same original Ga points, over every commutative value algebra. -/
theorem gaProductCoordinate_eval
    (x : ι → B →ₐc[K] SymmetricAlgebra K K) (l : List ι)
    {A : Type*} [CommRing A] [Algebra K A] (a : ι → A) :
    (MvPolynomial.aeval a).comp (gaProductCoordinate x l) =
      ((l.map (fun i => gaParameterPoint (x i) (a i))).prod).ofConv := by
  have h := map_list_prod (AlgHom.mapValue (MvPolynomial.aeval a))
    (l.map (fun i => gaParameterPoint (x i) (MvPolynomial.X i)))
  simp only [List.map_map, Function.comp_def, gaParameterPoint_mapValue,
    MvPolynomial.aeval_X] at h
  exact congrArg WithConv.ofConv h

/-- The ordered polynomial map lands in the generated closed
subgroup: it is the composite of a polynomial map on that quotient and
the original quotient coordinate map. -/
theorem gaProductCoordinate_factors
    (x : ι → B →ₐc[K] SymmetricAlgebra K K) (l : List ι) :
    (gaProductCoordinate (gaGeneratedLift x) l).comp
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (gaGeneratedHopfIdeal x)).hom.toAlgHom = gaProductCoordinate x l := by
  let q := (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
    (gaGeneratedHopfIdeal x)).hom
  have hf (i : ι) : AlgHom.mapDomain q
      (gaParameterPoint (gaGeneratedLift x i) (MvPolynomial.X i : MvPolynomial ι K)) =
        gaParameterPoint (x i) (MvPolynomial.X i : MvPolynomial ι K) := by
    unfold gaParameterPoint
    rw [← MonoidHom.comp_apply, ← AlgHom.mapDomain_comp, gaGeneratedLift_comp]
  have h := map_list_prod (AlgHom.mapDomain (A := MvPolynomial ι K) q)
    (l.map (fun i => gaParameterPoint (gaGeneratedLift x i)
      (MvPolynomial.X i : MvPolynomial ι K)))
  simp only [List.map_map, Function.comp_def, hf] at h
  exact congrArg WithConv.ofConv h

/-- The equality is

```lean
gaProductCoordinate x l b = 0
```
-/
theorem gaProductCoordinate_kills_generatedIdeal
    (x : ι → B →ₐc[K] SymmetricAlgebra K K) (l : List ι)
    (b : B) (hb : b ∈ gaGeneratedHopfIdeal x) : gaProductCoordinate x l b = 0 := by
  rw [← gaProductCoordinate_factors, AlgHom.comp_apply]
  change (gaProductCoordinate (gaGeneratedLift x) l)
    ((CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
      (gaGeneratedHopfIdeal x)).hom b) = 0
  rw [(CommHopfAlgCat.mkQuotient_eq_zero_iff
    (CommHopfAlgCat.of K B) (gaGeneratedHopfIdeal x) b).mpr hb, map_zero]

end ReductiveGroups
