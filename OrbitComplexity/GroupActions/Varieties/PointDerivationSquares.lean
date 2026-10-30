import OrbitComplexity.GroupActions.Varieties.PointDerivations

/-!
# Equivariant differential comparison

Coordinate automorphisms commuting with a morphism identify its point derivations.
Bijectivity therefore passes from a point to its translated point.

## Main results

* `GroupActions.bijective_pointPrecomp_equiv`: invariance under a commuting coordinate square.
-/

namespace GroupActions

noncomputable section

universe u v w x

variable {R : Type u} {S : Type v} {T : Type w} {C : Type x}
  [CommRing R] [CommRing S] [CommRing T] [CommRing C]
  [Algebra R S] [Algebra R T] [Algebra R C]

private theorem pointComp_eq (f : S →ₐ[R] T) (eS : S ≃ₐ[R] S) (eT : T ≃ₐ[R] T)
    (h : eT.toAlgHom.comp f = f.comp eS.toAlgHom) (p : T →ₐ[R] C) :
    (p.comp eT.toAlgHom).comp f = (p.comp f).comp eS.toAlgHom := by
  ext s
  exact congrArg p (AlgHom.congr_fun h s)

private theorem pointDerivationEquiv_natural (f : S →ₐ[R] T)
    (eS : S ≃ₐ[R] S) (eT : T ≃ₐ[R] T)
    (h : eT.toAlgHom.comp f = f.comp eS.toAlgHom) (p : T →ₐ[R] C)
    (d : Derivation R T (PointAlgebra p)) :
    pointDerivationEquiv eS (p.comp f) (pointDerivationPrecomp f p d) =
      pointDerivationCongr (pointComp_eq f eS eT h p)
        (pointDerivationPrecomp f (p.comp eT.toAlgHom) (pointDerivationEquiv eT p d)) := by
  ext s
  apply (PointAlgebra.algEquivSelf ((p.comp f).comp eS.toAlgHom)).injective
  have hL : PointAlgebra.algEquivSelf ((p.comp f).comp eS.toAlgHom)
      (pointDerivationEquiv eS (p.comp f) (pointDerivationPrecomp f p d) s) =
      PointAlgebra.algEquivSelf p (d (f (eS s))) := by
    rfl
  have hR : PointAlgebra.algEquivSelf ((p.comp f).comp eS.toAlgHom)
      (pointDerivationCongr (pointComp_eq f eS eT h p)
        (pointDerivationPrecomp f (p.comp eT.toAlgHom) (pointDerivationEquiv eT p d)) s) =
      PointAlgebra.algEquivSelf p (d (eT (f s))) := by
    erw [pointDerivationCongr_apply]
    rfl
  rw [hL, hR]
  exact congrArg (fun z => PointAlgebra.algEquivSelf p (d z)) (AlgHom.congr_fun h s).symm

/-- Coordinate equivalences commuting with a morphism preserve bijectivity of point derivatives. -/
theorem bijective_pointPrecomp_equiv (f : S →ₐ[R] T)
    (eS : S ≃ₐ[R] S) (eT : T ≃ₐ[R] T)
    (h : eT.toAlgHom.comp f = f.comp eS.toAlgHom) (p : T →ₐ[R] C) :
    Function.Bijective (pointDerivationPrecomp f p) ↔
      Function.Bijective (pointDerivationPrecomp f (p.comp eT.toAlgHom)) := by
  let eIn := pointDerivationEquiv eT p
  let eOld := pointDerivationEquiv eS (p.comp f)
  let eOut := pointDerivationCongr (pointComp_eq f eS eT h p)
  let old := pointDerivationPrecomp f p
  let new := pointDerivationPrecomp f (p.comp eT.toAlgHom)
  have hfun : eOld ∘ old = eOut ∘ new ∘ eIn :=
    funext (pointDerivationEquiv_natural f eS eT h p)
  calc
    Function.Bijective old ↔ Function.Bijective (eOld ∘ old) :=
      (EquivLike.comp_bijective old eOld).symm
    _ ↔ Function.Bijective (eOut ∘ new ∘ eIn) := by rw [hfun]
    _ ↔ Function.Bijective (new ∘ eIn) := EquivLike.comp_bijective _ eOut
    _ ↔ Function.Bijective new := EquivLike.bijective_comp eIn new

end

end GroupActions
