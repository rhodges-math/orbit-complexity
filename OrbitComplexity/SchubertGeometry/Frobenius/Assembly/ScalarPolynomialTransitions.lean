import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.MatchingScalarData
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Affine polynomial transitions on scalar chart models

The affine coordinate change commutes with a natural coefficient map.
The Cartesian square of the prescribed scalar model then identifies the
lifted chart transition from its old and scalar-base projections.
-/

set_option autoImplicit false
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace SchubertGeometry.RetainedCharacter

open private affinePolynomialMap affinePolynomialMap_apply from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingOperatorOverlaps

private theorem affinePolynomialMap_C {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : Bˣ) (b : B) (x : A) :
    affinePolynomialMap f a b (C x) = C (f x) := by
  rw [affinePolynomialMap_apply, Polynomial.map_C, Polynomial.C_comp]

private theorem affinePolynomialMap_scalar {T A B : Type u}
    [CommRing T] [CommRing A] [CommRing B] [Algebra T A] [Algebra T B]
    (f : A →ₐ[T] B) (a : Bˣ) (b : B) :
    (affinePolynomialMap f.toRingHom a b).comp (algebraMap T (Polynomial A)) =
      algebraMap T (Polynomial B) := by
  apply RingHom.ext
  intro t
  change affinePolynomialMap f.toRingHom a b (algebraMap T (Polynomial A) t) = _
  rw [Polynomial.algebraMap_apply, affinePolynomialMap_C]
  exact (congrArg Polynomial.C (f.commutes t)).trans
    (Polynomial.algebraMap_apply t).symm

private theorem affinePolynomialMap_square {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (f : A →+* B) (f' : A' →+* B') (μ : A →+* A') (ν : B →+* B')
    (h : f'.comp μ = ν.comp f) (a : Bˣ) (b : B) :
    (affinePolynomialMap f' (Units.map ν.toMonoidHom a) (ν b)).comp
        (Polynomial.mapRingHom μ) =
      (Polynomial.mapRingHom ν).comp (affinePolynomialMap f a b) := by
  apply RingHom.ext
  intro P
  change affinePolynomialMap f' (Units.map ν.toMonoidHom a) (ν b) (Polynomial.map μ P) =
    Polynomial.map ν (affinePolynomialMap f a b P)
  simp only [affinePolynomialMap_apply, Polynomial.map_map, h, Polynomial.map_comp,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Units.coe_map]
  rfl

private theorem scalarPolynomial_transition {S T A B A' B' : Type u}
    [CommRing S] [CommRing T] [Algebra S T]
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra T A'] [Algebra T B']
    (f : A →+* B) (f' : A' →ₐ[T] B') (μ : A →+* A') (ν : B →+* B')
    (h : f'.toRingHom.comp μ = ν.comp f) (a : Bˣ) (b : B)
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of S))
    (baseT : Y ⟶ Spec (.of T)) (q : Y ⟶ X)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (kA : Spec (.of (Polynomial A)) ⟶ X) (kB : Spec (.of (Polynomial B)) ⟶ X)
    (KA : Spec (.of (Polynomial A')) ⟶ Y) (KB : Spec (.of (Polynomial B')) ⟶ Y)
    (hAold : KA ≫ q = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom μ)) ≫ kA)
    (hBold : KB ≫ q = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom ν)) ≫ kB)
    (hAbase : KA ≫ baseT = Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial A'))))
    (hBbase : KB ≫ baseT = Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial B'))))
    (hold : Spec.map (CommRingCat.ofHom (affinePolynomialMap f a b)) ≫ kA = kB) :
    Spec.map (CommRingCat.ofHom (affinePolynomialMap f'.toRingHom
      (Units.map ν.toMonoidHom a) (ν b))) ≫ KA = KB := by
  let g := affinePolynomialMap f a b
  let g' := affinePolynomialMap f'.toRingHom (Units.map ν.toMonoidHom a) (ν b)
  have hring := affinePolynomialMap_square f f'.toRingHom μ ν h a b
  have hs : Spec.map (CommRingCat.ofHom g') ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom μ)) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom ν)) ≫
        Spec.map (CommRingCat.ofHom g) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hring
  apply hq.hom_ext
  · calc
      _ = Spec.map (CommRingCat.ofHom g') ≫ (KA ≫ q) := Category.assoc _ _ _
      _ = (Spec.map (CommRingCat.ofHom g') ≫
          Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom μ))) ≫ kA := by
        rw [hAold, Category.assoc]
      _ = (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom ν)) ≫
          Spec.map (CommRingCat.ofHom g)) ≫ kA := congrArg (fun f => f ≫ kA) hs
      _ = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom ν)) ≫ kB := by
        rw [Category.assoc, hold]
      _ = _ := hBold.symm
  · calc
      _ = Spec.map (CommRingCat.ofHom g') ≫ (KA ≫ baseT) := Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom g') ≫
          Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial A'))) :=
        congrArg (fun f => Spec.map (CommRingCat.ofHom g') ≫ f) hAbase
      _ = Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial B'))) := by
        rw [← Spec.map_comp]
        exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
          (affinePolynomialMap_scalar f' (Units.map ν.toMonoidHom a) (ν b))
      _ = _ := hBbase.symm

/-- The affine transition on a natural scalar coefficient diagram is the
transition of the prescribed scalar charts, with both projections retained. -/
theorem scalarDiagram_chart_transition {S T : Type u}
    [CommRing S] [CommRing T] [Algebra S T] {J : Type v} [Category J]
    (N : J ⥤ CommAlgCat.{u} S) (M : J ⥤ CommAlgCat.{u} T)
    (μ : N ⋙ forget₂ (CommAlgCat S) CommRingCat ⟶
      M ⋙ forget₂ (CommAlgCat T) CommRingCat)
    {s t : J} (f : s ⟶ t) (a : (N.obj t)ˣ) (b : N.obj t)
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of S))
    (baseT : Y ⟶ Spec (.of T)) (q : Y ⟶ X)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (kA : Spec (.of (Polynomial (N.obj s))) ⟶ X)
    (kB : Spec (.of (Polynomial (N.obj t))) ⟶ X)
    (KA : Spec (.of (Polynomial (M.obj s))) ⟶ Y)
    (KB : Spec (.of (Polynomial (M.obj t))) ⟶ Y)
    (hAold : KA ≫ q = Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (μ.app s).hom)) ≫ kA)
    (hBold : KB ≫ q = Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (μ.app t).hom)) ≫ kB)
    (hAbase : KA ≫ baseT =
      Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (M.obj s)))))
    (hBbase : KB ≫ baseT =
      Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (M.obj t)))))
    (hold : Spec.map (CommRingCat.ofHom
      (affinePolynomialMap (N.map f).hom.toRingHom a b)) ≫ kA = kB) :
    Spec.map (CommRingCat.ofHom (affinePolynomialMap (M.map f).hom.toRingHom
      (Units.map (μ.app t).hom.toMonoidHom a) ((μ.app t).hom b))) ≫ KA = KB := by
  have h : (M.map f).hom.toRingHom.comp (μ.app s).hom =
      (μ.app t).hom.comp (N.map f).hom.toRingHom := by
    exact congrArg (fun f : CommRingCat.of (N.obj s) ⟶ CommRingCat.of (M.obj t) => f.hom)
      (μ.naturality f).symm
  exact scalarPolynomial_transition (N.map f).hom.toRingHom (M.map f).hom
    (μ.app s).hom (μ.app t).hom h a b base baseT q hq kA kB KA KB
    hAold hBold hAbase hBbase hold

end SchubertGeometry.RetainedCharacter
