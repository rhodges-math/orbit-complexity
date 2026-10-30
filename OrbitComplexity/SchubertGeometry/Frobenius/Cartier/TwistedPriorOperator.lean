import OrbitComplexity.FrobeniusSplitting.Modules.Frobenius
import OrbitComplexity.FrobeniusSplitting.Splittings.SheafOperators
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport

/-! # Coefficient operators of the twisted prior map

The global map has the character line as its source. Its coefficient operators
therefore transform with the line frames. A global section is inserted
once, only when constructing the structure-sheaf operator.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

variable {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
variable {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)

private abbrev frobeniusLine := frobeniusRestriction C p base L

/-- A local section of the original character line gives the coefficient
operator of the unweighted global twisted prior map. -/
def twistedFrameOperator
    (Θ : frobeniusLine (p := p) base L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (e : Γ(L, U)) : FrobeniusLinearMap Γ(X, U) p where
  toAddMonoidHom :=
    { toFun a := (Θ.val.app (op U)).hom (a • e)
      map_zero' := by
        rw [zero_smul]
        exact (Θ.val.app (op U)).hom.map_zero
      map_add' a b := by
        rw [add_smul]
        exact (Θ.val.app (op U)).hom.map_add (a • e) (b • e) }
  map_pow_mul' a b := by
    let z : Γ(X, U) := (Θ.val.app (op U)).hom (b • e)
    have hm := (Θ.val.app (op U)).hom.map_smul a (b • e)
    change (Θ.val.app (op U)).hom ((a ^ p) • (b • e)) = a * z at hm
    change (Θ.val.app (op U)).hom ((a ^ p * b) • e) = a * z
    simpa only [mul_smul] using hm

/-- If the frames satisfy `res(e)=g·e'`, their constructed coefficient
operators satisfy the corresponding twisted restriction identity. -/
theorem twistedFrameOperator_restrict
    (Θ : frobeniusLine (p := p) base L ⟶ SheafOfModules.unit X.ringCatSheaf)
    {U V : X.Opens} (h : V ≤ U) (e : Γ(L, U)) (e' : Γ(L, V)) (g : Γ(X, V))
    (he : L.presheaf.map (homOfLE h).op e = g • e') (a : Γ(X, U)) :
    twistedFrameOperator base L Θ V e' (g * X.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE h).op (twistedFrameOperator base L Θ U e a) := by
  have hn := ConcreteCategory.congr_hom
    (Θ.mapPresheaf.naturality (homOfLE h).op) (a • e)
  change Θ.app V (L.presheaf.map (homOfLE h).op (a • e)) =
    X.presheaf.map (homOfLE h).op (Θ.app U (a • e)) at hn
  change Θ.app V ((g * X.presheaf.map (homOfLE h).op a) • e') =
    X.presheaf.map (homOfLE h).op (Θ.app U (a • e))
  rw [← hn]
  congr 1
  calc
    _ = X.presheaf.map (homOfLE h).op a • (g • e') := by
      rw [mul_comm g, mul_smul]
    _ = X.presheaf.map (homOfLE h).op a • L.presheaf.map (homOfLE h).op e := by
      rw [he]
    _ = _ := (L.map_smul (homOfLE h) a e).symm

/-- Inserting the same global section once into the twisted prior map produces
an global operator on the structure sheaf. -/
def twistedSectionOperator
    (Θ : frobeniusLine (p := p) base L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : Γ(L, ⊤)) : SchemeFrobeniusMap X p where
  onOpen U := twistedFrameOperator base L Θ U
    (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)
  restrict_comm {U V} h a := by
    let e := L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s
    let e' := L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s
    have he : L.presheaf.map (homOfLE h).op e = (1 : Γ(X, V)) • e' := by
      dsimp only [e, e']
      rw [one_smul, ← CategoryTheory.comp_apply, ← CategoryTheory.Functor.map_comp]
      rfl
    simpa only [one_mul] using
      twistedFrameOperator_restrict base L Θ h e e' 1 he a

/-- In an line frame, the section enters as one input weight, rather than
being inserted into an already weighted prior splitting a second time. -/
theorem twistedSectionOperator_frame
    (Θ : frobeniusLine (p := p) base L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : Γ(L, ⊤)) (U : X.Opens) (e : Γ(L, U)) (f : Γ(X, U))
    (hs : L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s = f • e)
    (a : Γ(X, U)) :
    (twistedSectionOperator base L Θ s).onOpen U a =
      (twistedFrameOperator base L Θ U e).weight f a := by
  change Θ.app U (a • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) =
    Θ.app U ((f * a) • e)
  rw [hs, mul_comm f a, mul_smul]

/-- The only normalization value is the twisted map on the original section. -/
theorem twistedSectionOperator_one
    (Θ : frobeniusLine (p := p) base L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : Γ(L, ⊤)) :
    (twistedSectionOperator base L Θ s).onOpen ⊤ 1 = Θ.app ⊤ s := by
  change Θ.app ⊤ ((1 : Γ(X, ⊤)) • L.presheaf.map (𝟙 (op ⊤)) s) = Θ.app ⊤ s
  rw [CategoryTheory.Functor.map_id, CategoryTheory.id_apply, one_smul]

end SchubertGeometry.ProjectiveCartier
