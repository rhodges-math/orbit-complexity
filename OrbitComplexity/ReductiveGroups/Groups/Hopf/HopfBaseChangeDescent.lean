import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange

/-!
# Hopf Base Change Descent

Descent of a Hopf-algebra isomorphism across an equivalence of base fields. -/

noncomputable section
namespace ReductiveGroups

open CategoryTheory

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- If the extension field is equivalent to the base field, an isomorphism
after scalar extension already gives an isomorphism over the base field. -/
def hopfIsoOfBaseChangeIso (r : K ≃ₐ[K] L)
    (A B : CommHopfAlgCat.{u} K)
    (e : TauCeti.CommHopfAlgCat.baseChange (K := L) A ≅
      TauCeti.CommHopfAlgCat.baseChange (K := L) B) : A ≅ B := by
  let : Algebra L K := r.symm.toAlgHom.toAlgebra
  let : IsScalarTower K L K := IsScalarTower.of_algHom r.symm.toAlgHom
  exact
    (CommHopfAlgCat.isoMk (Bialgebra.TensorProduct.lid K A)).symm ≪≫
    (TauCeti.CommHopfAlgCat.baseChangeTowerIso (E := L) K K A).symm ≪≫
    (TauCeti.CommHopfAlgCat.baseChangeFunctor (K := K)).mapIso e ≪≫
    (TauCeti.CommHopfAlgCat.baseChangeTowerIso (E := L) K K B) ≪≫
    CommHopfAlgCat.isoMk (Bialgebra.TensorProduct.lid K B)

end ReductiveGroups
