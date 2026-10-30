import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.ProjectiveCoordinates
import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.InfinityGenerators
import OrbitComplexity.FrobeniusSplitting.Splittings.PolynomialOperators

/-! # The line-source relative Cartier map on the original charts

The source is the Frobenius restriction of the degree `p-1` line. Its specified
infinity factor is applied before the trace. Only the ground field is perfect;
the coefficient algebra and the prior coefficient operator are arbitrary.
-/

open AlgebraicGeometry CategoryTheory Opposite
open GroupActions FrobeniusSplitting FrobeniusSplitting.OperatorSheaf
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

private def twistedOverComponent {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (M N : X.Modules) (U : X.Opens)
    (k : M.over U ⟶ N.over U) (V : (Over U)ᵒᵖ) :
    ((frobeniusRestriction C p base M).over U).val.obj V ⟶
      ((frobeniusRestriction C p base N).over U).val.obj V :=
  { hom' :=
      { toFun := fun s => (k.val.app V).hom s
        map_add' := fun s t => (k.val.app V).hom.map_add s t
        map_smul' := fun r s => by
          let a : Γ(X, V.unop.left) := r
          exact (k.val.app V).hom.map_smul (a ^ p) s } }

private def twistedOverMap {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (M N : X.Modules) (U : X.Opens)
    (k : M.over U ⟶ N.over U) :
    (frobeniusRestriction C p base M).over U ⟶
      (frobeniusRestriction C p base N).over U where
  val :=
    { app := fun V => twistedOverComponent base M N U k V
      naturality := fun {V W} f => by
        ext s
        exact ConcreteCategory.congr_hom (k.val.naturality f) s }

private theorem twistedOverMap_comp_apply {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {X : Scheme.{u}} (base : X ⟶ Spec (.of C))
    (M N P : X.Modules) (U : X.Opens) (k : M.over U ⟶ N.over U)
    (l : (frobeniusRestriction C p base N).over U ⟶ P.over U)
    (V : Over U) (s : M.val.obj (op V.left)) :
    ((twistedOverMap base M N U k ≫ l).val.app (op V)).hom s =
      (l.val.app (op V)).hom ((k.val.app (op V)).hom s) := rfl

private abbrev indices : Type u := ULift.{u} (Fin 2)

private abbrev line (A : Type u) [CommRing A] : Scheme.{u} :=
  projectiveScheme A indices.{u}

private abbrev affine (A : Type u) [CommRing A] : Scheme.{u} := Spec (.of (Polynomial A))

private abbrev chart (A : Type u) [CommRing A] (j : indices.{u}) : affine A ⟶ line A :=
  projectiveLinePolynomialChart A j

private abbrev chartOpen (A : Type u) [CommRing A] (j : indices.{u}) : (line A).Opens :=
  (chart A j).opensRange

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

private def relativeBase : line A ⟶ Spec (.of K) :=
  projectiveToSpec A indices.{u} ≫ Spec.map (CommRingCat.ofHom (algebraMap K A))

private abbrev sourceLine : (line A).Modules :=
  SchubertGeometry.ProjectiveLine.projectiveTransitionModule A (p - 1)

private abbrev unitLine : (line A).Modules := SheafOfModules.unit (line A).ringCatSheaf

private def relativeTrace (ψ : FrobeniusLinearMap A p) (j : indices.{u}) :
    localOperators (sheafFrobenius K p (relativeBase (K := K) (A := A)))
      (chartOpen A j) :=
  let τ : SchemeFrobeniusMap (affine A) p :=
    (polynomialTraceOfOperator (K := K) ψ).toSpec (expChar_pos K p)
  let τU : SchemeFrobeniusMap (chartOpen A j).toScheme p :=
    τ.pushforward (chart A j).isoOpensRange.hom
  (openOperatorEquiv K p (relativeBase (K := K) (A := A)) (chartOpen A j)).symm τU

private def infinityCoefficient (j : indices.{u}) :
    (sourceLine (A := A) (p := p)).over (chartOpen A j) ⟶
      (unitLine (A := A)).over (chartOpen A j) :=
  let U : (line A).Opens := chartOpen A j
  let M : (line A).Modules :=
    SchubertGeometry.ProjectiveLine.projectiveTransitionModule A (2 * (p - 1))
  let f : (sourceLine (A := A) (p := p)).over U ⟶ M.over U :=
    (SchubertGeometry.ProjectiveLine.projectiveInfinityFactor A (p - 1)).over U
  let g : M.over U ⟶ (unitLine (A := A)).over U := projectiveCartierCoefficient A p j
  f ≫ g

/-- In each original polynomial chart, the prior operator constructs a map from
the Frobenius-restricted endpoint line. The infinity factor enters once. -/
def relativeTwistedCartierChart (ψ : FrobeniusLinearMap A p) (j : indices.{u}) :
    (frobeniusRestriction K p (relativeBase (K := K) (A := A))
      (sourceLine (A := A) (p := p))).over (chartOpen A j) ⟶
        (unitLine (A := A)).over (chartOpen A j) :=
  twistedOverMap (relativeBase (K := K) (A := A))
      (sourceLine (A := A) (p := p)) (unitLine (A := A)) (chartOpen A j)
      (infinityCoefficient (A := A) (p := p) j) ≫ relativeTrace (K := K) ψ j

private theorem infinityCoefficient_value (j : indices.{u}) (V : Over (chartOpen A j))
    (s : (sourceLine (A := A) (p := p)).val.obj (op V.left)) :
    (show Γ(line A, V.left) from
      ((infinityCoefficient (A := A) (p := p) j).val.app (op V)).hom s) =
      (show Γ(line A, V.left) from
        (((SchubertGeometry.ProjectiveLine.projectiveInfinityFactor A (p - 1)).over
            (chartOpen A j) ≫ projectiveCartierCoefficient A p j).val.app (op V)).hom s) :=
  rfl

private theorem relativeTrace_value (ψ : FrobeniusLinearMap A p) (j : indices.{u})
    (V : Over (chartOpen A j)) (a : Γ(line A, V.left)) :
    (show Γ(line A, V.left) from
      ((relativeTrace (K := K) ψ j).val.app (op V)).hom a) =
      (show Γ(line A, V.left) from
        (((openOperatorEquiv K p (relativeBase (K := K) (A := A)) (chartOpen A j)).symm
          (((polynomialTraceOfOperator (K := K) ψ).toSpec (expChar_pos K p)).pushforward
            (chart A j).isoOpensRange.hom)).val.app (op V)).hom a) := rfl

private theorem relativeChart_value (ψ : FrobeniusLinearMap A p) (j : indices.{u})
    (V : Over (chartOpen A j))
    (s : (sourceLine (A := A) (p := p)).val.obj (op V.left)) :
    (show Γ(line A, V.left) from
      ((relativeTwistedCartierChart (K := K) ψ j).val.app (op V)).hom s) =
      (show Γ(line A, V.left) from
        ((relativeTrace (K := K) ψ j).val.app (op V)).hom
          (((infinityCoefficient (A := A) (p := p) j).val.app (op V)).hom s)) :=
  twistedOverMap_comp_apply (relativeBase (K := K) (A := A))
    (sourceLine (A := A) (p := p)) (unitLine (A := A)) (unitLine (A := A))
    (chartOpen A j) (infinityCoefficient (A := A) (p := p) j)
    (relativeTrace (K := K) ψ j) V s

end SchubertGeometry.ProjectiveCartier
