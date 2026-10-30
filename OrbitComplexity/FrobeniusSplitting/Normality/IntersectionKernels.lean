import OrbitComplexity.FrobeniusSplitting.Normality.Models.ClosedChartQuotients
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Batteries.Tactic.Lint
import Batteries.Tactic.OpenPrivate

/-! # Kernels on affine intersections -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open private preimage_intersection from
  OrbitComplexity.FrobeniusSplitting.Normality.Models.ClosedChartQuotients

namespace FrobeniusSplitting

universe u

private theorem arrow_ker_comap
    {A B C D : CommRingCat.{u}} (f : A ⟶ B) (g : C ⟶ D)
    (eA : A ≅ C) (eB : B ≅ D) (h : eA.hom ≫ g = f ≫ eB.hom) :
    RingHom.ker f.hom = (RingHom.ker g.hom).comap eA.hom.hom := by
  have hcomp : g.hom.comp eA.hom.hom = eB.hom.hom.comp f.hom :=
    congrArg (fun k : A ⟶ D => k.hom) h
  calc
    RingHom.ker f.hom = RingHom.ker (eB.hom.hom.comp f.hom) :=
      (RingHom.ker_comp_of_injective f.hom
        (ConcreteCategory.bijective_of_isIso eB.hom).1).symm
    _ = RingHom.ker (g.hom.comp eA.hom.hom) := congrArg RingHom.ker hcomp.symm
    _ = (RingHom.ker g.hom).comap eA.hom.hom :=
      (RingHom.comap_ker _ _).symm

private theorem resLE_kernel {X Y : Scheme.{u}} (j : Y ⟶ X) [QuasiCompact j]
    (U : X.affineOpens) (V : Y.Opens) (hV : V = j ⁻¹ᵁ U.1) :
    RingHom.ker (j.resLE U.1 V hV.le).appTop.hom =
      (j.ker.ideal U).comap U.1.topIso.hom.hom := by
  subst V
  have square := (AlgebraicGeometry.arrowResLEAppIso j U.1 (j ⁻¹ᵁ U.1) le_rfl).hom.w
  have result := arrow_ker_comap
    (j.resLE U.1 (j ⁻¹ᵁ U.1) le_rfl).appTop
    (j.appLE U.1 (j ⁻¹ᵁ U.1) le_rfl) U.1.topIso (j ⁻¹ᵁ U.1).topIso square
  rw [Scheme.Hom.appLE_eq_app, ← Scheme.Hom.ker_apply] at result
  exact result

/-- The coordinate map of inverse-image intersections has the original
scheme-theoretic image ideal as its kernel, transported by the canonical
isomorphism between the two rings of sections of the target open. -/
theorem intersectionCoordinateMap_ker {X Y : Scheme.{u}} {T K : Type u}
    [CommRing K] [IsAffineHom (CategoryTheory.Limits.pullback.diagonal (terminal.from X))]
    (j : Y ⟶ X) [QuasiCompact j] (base : X ⟶ Spec (.of K))
    (U : T → X.Opens) (hU : ∀ t, IsAffineOpen (U t))
    (s : {s : Finset T // s.Nonempty}) :
    RingHom.ker
      (((intersectionCoordinateMap j base (fun t => j ⁻¹ᵁ U t) U id
        (fun _ => le_rfl)).app s).hom.toRingHom) =
      (j.ker.ideal ⟨(intersectionOpens U).obj
        ((intersectionIndexMap (id : T → T)).op.obj (op s)),
        intersectionOpens_affine U hU _⟩).comap
          ((intersectionOpens U).obj
            ((intersectionIndexMap (id : T → T)).op.obj (op s))).topIso.hom.hom := by
  change RingHom.ker
    (j.resLE
      ((intersectionOpens U).obj ((intersectionIndexMap (id : T → T)).op.obj (op s)))
      ((intersectionOpens (fun t => j ⁻¹ᵁ U t)).obj (op s))
      (intersection_preimage_le j (fun t => j ⁻¹ᵁ U t) U id
        (fun _ => le_rfl) (op s))).appTop.hom = _
  exact resLE_kernel j
    ⟨(intersectionOpens U).obj ((intersectionIndexMap (id : T → T)).op.obj (op s)),
      intersectionOpens_affine U hU _⟩
    ((intersectionOpens (fun t => j ⁻¹ᵁ U t)).obj (op s))
    (preimage_intersection j U (op s))

end FrobeniusSplitting
