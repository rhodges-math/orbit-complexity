import Batteries.Tactic.Lint
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Scheme endpoints of polynomial contractions

The endpoint and chart comparisons are proved for arbitrary coefficient rings,
coordinate rings and schemes. Applications supply ring equations and a chart
square to these lemmas, without asking the kernel to identify concrete scheme
maps.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FrobeniusSplitting

universe u

private theorem spec_comp_of_eq
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (q : A →+* B) (f : B →+* C) (g : A →+* C)
    (h : f.comp q = g) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom q) =
      Spec.map (CommRingCat.ofHom g) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

variable {K C : Type u} [CommRing K] [CommRing C] [Algebra K C]

/-- A descended origin has the same ambient image through any commuting pair of
affine charts. The schemes and all coordinate maps are arbitrary. -/
theorem originChart_image
    {A : Type u} [CommRing A] [Algebra K A]
    (q : A →ₐ[K] C) (o : C →ₐ[K] K) (ε : A →ₐ[K] K)
    (hOrigin : o.comp q = ε)
    {X Y : Scheme.{u}} (eA : Spec (.of A) ≅ X) (eC : Spec (.of C) ≅ Y)
    (i : Y ⟶ X)
    (hSquare : Spec.map (CommRingCat.ofHom q.toRingHom) ≫ eA.hom =
      eC.hom ≫ i) :
    Spec.map (CommRingCat.ofHom o.toRingHom) ≫ eC.hom ≫ i =
      Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ eA.hom := by
  have hRing : o.toRingHom.comp q.toRingHom = ε.toRingHom := by
    apply RingHom.ext
    intro a
    exact congrArg (fun f : A →ₐ[K] K => f a) hOrigin
  have hSpec : Spec.map (CommRingCat.ofHom o.toRingHom) ≫
      Spec.map (CommRingCat.ofHom q.toRingHom) =
        Spec.map (CommRingCat.ofHom ε.toRingHom) :=
    spec_comp_of_eq q.toRingHom o.toRingHom ε.toRingHom hRing
  calc
    Spec.map (CommRingCat.ofHom o.toRingHom) ≫ eC.hom ≫ i =
        Spec.map (CommRingCat.ofHom o.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom q.toRingHom) ≫ eA.hom) :=
      congrArg (fun f => Spec.map (CommRingCat.ofHom o.toRingHom) ≫ f)
        hSquare.symm
    _ = (Spec.map (CommRingCat.ofHom o.toRingHom) ≫
        Spec.map (CommRingCat.ofHom q.toRingHom)) ≫ eA.hom :=
      (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ eA.hom :=
      congrArg (fun f => f ≫ eA.hom) hSpec

end FrobeniusSplitting
