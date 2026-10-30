import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendLiftEvaluation
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingCoframeEvaluation
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CharacterFramePowers
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # The common unit for all append coframe powers

The prescribed polynomial chart factor determines a map over the coefficient
field from its endpoint equation. Comparing its regular append lift with the
chosen endpoint lift constructs one Borel unit. Character evaluation then
identifies every append coframe power with the matching coframe multiplied
by that unit to the same power.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open scoped CategoryTheory.MonObj

noncomputable section
universe u v w

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift lift_quotient
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private comparisonCoframe fieldAppendCoframe
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
open private polynomialBase
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
open private appendPolynomialLift appendPolynomialLift_endpoint
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoframes
open private CoframeTransport.pullCoframe CoframeTransport.evaluation_base_change
  CoframeTransport.iso_app_eqToHom
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.CoframeTransport
open private section_character_power
  from OrbitComplexity.SchubertGeometry.Normality.BottSamelson.CharacterCoefficients

private theorem endpoint_factor {C : Type v} [Category.{w} C]
    {P Q X Y H Z : C} (a : Q ⟶ H) (b : P ⟶ H) (t : H ⟶ Z)
    (j : P ⟶ X) (q : X ⟶ Y) (k : P ⟶ Q) (r : Q ⟶ Y) (z : Y ⟶ Z)
    (ha : a ≫ t = r ≫ z) (hb : b ≫ t = j ≫ q ≫ z)
    (hk : j ≫ q = k ≫ r) : k ≫ a ≫ t = b ≫ t := by
  calc
    _ = k ≫ r ≫ z := congrArg (fun x => k ≫ x) ha
    _ = (k ≫ r) ≫ z := (Category.assoc _ _ _).symm
    _ = (j ≫ q) ≫ z := congrArg (fun x => x ≫ z) hk.symm
    _ = j ≫ q ≫ z := Category.assoc _ _ _
    _ = _ := hb.symm

private theorem over_scalar {S : Scheme.{u}} {P Q H Z : Over S}
    (f : P.left ⟶ Q.left) (a : Q ⟶ H) (b : P ⟶ H) (t : H ⟶ Z)
    (h : f ≫ a.left ≫ t.left = b.left ≫ t.left) : f ≫ Q.hom = P.hom := by
  have hz := congrArg (fun x => x ≫ Z.hom) h
  simpa only [Category.assoc, t.w, a.w, b.w] using hz

private def endpointMap {S : Scheme.{u}} {P Q H Z : Over S}
    (f : P.left ⟶ Q.left) (a : Q ⟶ H) (b : P ⟶ H) (t : H ⟶ Z)
    (h : f ≫ a.left ≫ t.left = b.left ≫ t.left) : P ⟶ Q :=
  Over.homMk f (over_scalar f a b t h)

private theorem composite_quotient {C : Type v} [Category.{w} C]
    {P Q Y H Z : C} (k : P ⟶ Q) (a : Q ⟶ H) (t : H ⟶ Z)
    (r : Q ⟶ Y) (d : P ⟶ Y) (z : Y ⟶ Z)
    (ha : a ≫ t = r ≫ z) (hk : k ≫ r = d) : (k ≫ a) ≫ t = d ≫ z :=
  (Category.assoc k a t).trans ((congrArg (fun x => k ≫ x) ha).trans
    ((Category.assoc k r z).symm.trans (congrArg (fun x => x ≫ z) hk)))

private theorem comparison_hom {P X Y Q : Scheme.{u}}
    (j : P ⟶ X) (q : X ⟶ Y) (k : P ⟶ Q) (r : Q ⟶ Y)
    (h : j ≫ q = k ≫ r) (M : X.Modules) (N : Y.Modules)
    (E : M ≅ (Scheme.Modules.pullback q).obj N)
    (e : (Scheme.Modules.pullback r).obj N ≅ SheafOfModules.unit Q.ringCatSheaf) :
    (Scheme.Modules.pullback j).map E.inv ≫
        (comparisonCoframe j q k r h M N E e).hom =
      (Scheme.Modules.pullbackComp j q).hom.app N ≫
        (Scheme.Modules.pullbackCongr h).hom.app N ≫
        CoframeTransport.pullCoframe k r N e.hom := by
  change ((Scheme.Modules.pullback j).mapIso E).inv ≫
    ((Scheme.Modules.pullback j).mapIso E).hom ≫ _ = _
  exact Iso.inv_hom_id_assoc _ _

private theorem compose_coframe {C : Type v} [Category.{w} C]
    {P A B Q E T : C} (a : P ⟶ A) (b : A ⟶ B)
    (c : P ⟶ Q) (d : Q ⟶ E) (w : E ⟶ B) (e : B ⟶ T) (f : E ⟶ T)
    (h : a ≫ b = c ≫ d ≫ w) (he : w ≫ e = f) :
    a ≫ b ≫ e = c ≫ d ≫ f := by
  simpa only [Category.assoc, he] using congrArg (fun t => t ≫ e) h

private theorem associate_coframe {X Y Z W : Scheme.{u}}
    (j : X ⟶ Y) (q : Y ⟶ Z) (z : Z ⟶ W) (M : W.Modules)
    {T : X.Modules} (e : (Scheme.Modules.pullback (j ≫ q ≫ z)).obj M ⟶ T)
    (f : (Scheme.Modules.pullback ((j ≫ q) ≫ z)).obj M ⟶ T)
    (he : (Scheme.Modules.pullbackCongr (Category.assoc j q z)).hom.app M ≫ e = f) :
    (Scheme.Modules.pullback j).map ((Scheme.Modules.pullbackComp q z).hom.app M) ≫
        (Scheme.Modules.pullbackComp j (q ≫ z)).hom.app M ≫ e =
      (Scheme.Modules.pullbackComp j q).hom.app ((Scheme.Modules.pullback z).obj M) ≫
        (Scheme.Modules.pullbackComp (j ≫ q) z).hom.app M ≫ f := by
  have hc : (Scheme.Modules.pullbackCongr (Category.assoc j q z)).hom.app M =
      eqToHom (congrArg (fun t : X ⟶ W => (Scheme.Modules.pullback t).obj M)
        (Category.assoc j q z)) := CoframeTransport.iso_app_eqToHom _ M
  have ht := Scheme.Modules.pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app j q z M
  have hv := congrArg (fun t =>
    (Scheme.Modules.pullbackComp j q).hom.app ((Scheme.Modules.pullback z).obj M) ≫
      (Scheme.Modules.pullbackComp (j ≫ q) z).hom.app M ≫ t) hc.symm
  exact compose_coframe
    ((Scheme.Modules.pullback j).map ((Scheme.Modules.pullbackComp q z).hom.app M))
    ((Scheme.Modules.pullbackComp j (q ≫ z)).hom.app M)
    ((Scheme.Modules.pullbackComp j q).hom.app ((Scheme.Modules.pullback z).obj M))
    ((Scheme.Modules.pullbackComp (j ≫ q) z).hom.app M)
    ((Scheme.Modules.pullbackCongr (Category.assoc j q z)).hom.app M) e f
    (ht.trans hv) he

private theorem unit_scalar_top (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    ((Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r).val.app
      (op ⊤)).hom (1 : Γ(X, ⊤)) = r := by
  have hle : (⊤ : X.Opens).leTop.op = 𝟙 (op (⊤ : X.Opens)) := Subsingleton.elim _ _
  have hm : X.presheaf.map (⊤ : X.Opens).leTop.op = 𝟙 (Γ(X, ⊤)) :=
    (congrArg X.presheaf.map hle).trans (CategoryTheory.Functor.map_id X.presheaf _)
  change X.presheaf.map (⊤ : X.Opens).leTop.op r * 1 = r
  exact (mul_one _).trans (ConcreteCategory.congr_hom hm r)

private theorem unit_ratio_from_scalar (A : Type u) [CommRing A]
    {L : (Spec (.of A)).Modules}
    (e f : L ≅ SheafOfModules.unit (Spec (.of A)).ringCatSheaf) (c : Aˣ)
    (h : f.hom = e.hom ≫ Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of A)).ringCatSheaf) ((Scheme.ΓSpecIso (.of A)).inv (c : A))) :
    FrobeniusSplitting.affineCoframeUnit A e f = c := by
  apply Units.ext
  let x := (e.inv.val.app (op ⊤)).hom (1 : Γ(Spec (.of A), ⊤))
  have he : (e.hom.val.app (op ⊤)).hom x = (1 : Γ(Spec (.of A), ⊤)) :=
    congrArg (fun t : SheafOfModules.unit (Spec (.of A)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (.of A)).ringCatSheaf =>
        (t.val.app (op ⊤)).hom (1 : Γ(Spec (.of A), ⊤))) e.inv_hom_id
  have hf : (f.hom.val.app (op ⊤)).hom x =
      ((Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of A)).inv (c : A))).val.app (op ⊤)).hom
          ((e.hom.val.app (op ⊤)).hom x) :=
    congrArg (fun t : L ⟶ SheafOfModules.unit (Spec (.of A)).ringCatSheaf =>
      (t.val.app (op ⊤)).hom x) h
  have hv := hf.trans ((congrArg
    (((Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of A)).inv (c : A))).val.app (op ⊤)).hom) he).trans
        (unit_scalar_top (Spec (.of A)) ((Scheme.ΓSpecIso (.of A)).inv (c : A))))
  exact (FrobeniusSplitting.affineCoframeUnit_value A e f).trans
    ((congrArg (Scheme.ΓSpecIso (.of A)).hom hv).trans
      (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of A)).inv_hom_id (c : A)))

/- `unit_ratio_from_scalar` with the scalar written as a first power, so that the degree-one
ratio applies as stated. Removing the power at the chart with `simpa only [pow_one] using` the
ratio fails there (a type mismatch after simplification); here it is removed generically. -/
private theorem unit_ratio_from_power_one (A : Type u) [CommRing A]
    {L : (Spec (.of A)).Modules}
    (e f : L ≅ SheafOfModules.unit (Spec (.of A)).ringCatSheaf) (c : Aˣ)
    (h : f.hom = e.hom ≫ Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of A)).inv ((c : A) ^ 1))) :
    FrobeniusSplitting.affineCoframeUnit A e f = c :=
  unit_ratio_from_scalar A e f c (by simpa only [pow_one] using h)


private theorem comparison_evaluation {P X Y Q : Scheme.{u}}
    {j : P ⟶ X} {q : X ⟶ Y} {k : P ⟶ Q} {r : Q ⟶ Y}
    (h : j ≫ q = k ≫ r) {M : X.Modules} {N : Y.Modules}
    (E : M ≅ (Scheme.Modules.pullback q).obj N)
    (e : (Scheme.Modules.pullback r).obj N ≅ SheafOfModules.unit Q.ringCatSheaf)
    {e' : (Scheme.Modules.pullback r).obj N ⟶ SheafOfModules.unit Q.ringCatSheaf}
    (he : e.hom = e') :
    (Scheme.Modules.pullback j).map E.inv ≫
        (comparisonCoframe j q k r h M N E e).hom =
      (Scheme.Modules.pullbackComp j q).hom.app N ≫
        (Scheme.Modules.pullbackCongr h).hom.app N ≫
        CoframeTransport.pullCoframe k r N e' := by
  exact (comparison_hom j q k r h M N E e).trans
    (congrArg (fun t => (Scheme.Modules.pullbackComp j q).hom.app N ≫
      (Scheme.Modules.pullbackCongr h).hom.app N ≫
      CoframeTransport.pullCoframe k r N t) he)


private theorem comparison_finish {P X Y Q : Scheme.{u}}
    {j : P ⟶ X} {q : X ⟶ Y} {k : P ⟶ Q} {r : Q ⟶ Y}
    (h : j ≫ q = k ≫ r) {M : X.Modules} {N : Y.Modules}
    (E : M ≅ (Scheme.Modules.pullback q).obj N)
    (e : (Scheme.Modules.pullback r).obj N ≅ SheafOfModules.unit Q.ringCatSheaf)
    {e' : (Scheme.Modules.pullback r).obj N ⟶ SheafOfModules.unit Q.ringCatSheaf}
    (he : e.hom = e')
    {t : (Scheme.Modules.pullback (j ≫ q)).obj N ⟶ SheafOfModules.unit P.ringCatSheaf}
    (ht : (Scheme.Modules.pullbackCongr h).hom.app N ≫
      CoframeTransport.pullCoframe k r N e' = t) :
    (Scheme.Modules.pullback j).map E.inv ≫
        (comparisonCoframe j q k r h M N E e).hom =
      (Scheme.Modules.pullbackComp j q).hom.app N ≫ t := by
  exact (comparison_evaluation h E e he).trans
    (congrArg (fun z => (Scheme.Modules.pullbackComp j q).hom.app N ≫ z) ht)

private theorem factorization_arrow {P X Y Q : Scheme.{u}}
    {j : P ⟶ X} {q : X ⟶ Y} {k k' : P ⟶ Q} {r : Q ⟶ Y}
    (hleft : k' = k) (h : j ≫ q = k ≫ r) : j ≫ q = k' ≫ r :=
  h.trans (congrArg (fun z => z ≫ r) hleft.symm)

private def coframeCast {P Y : Scheme.{u}} (r : P ⟶ Y)
    {N N' : Y.Modules} (hN : N = N')
    (e : (Scheme.Modules.pullback r).obj N ⟶ SheafOfModules.unit P.ringCatSheaf) :
    (Scheme.Modules.pullback r).obj N' ⟶ SheafOfModules.unit P.ringCatSheaf := hN ▸ e

/- A coframe cast is heterogeneously equal to the coframe. Used to remove the cast from
`comparison_export` as an equation between whole maps, with the cast's equation and modules
taken by unification from that result; normalizing the cast inside the composite, or restating
it with one spelling of the module, makes the kernel evaluate the coframes at the chart. -/
private theorem coframeCast_heq {P Y : Scheme.{u}} (r : P ⟶ Y) {N N' : Y.Modules} (h : N = N')
    (e : (Scheme.Modules.pullback r).obj N ⟶ SheafOfModules.unit P.ringCatSheaf) :
    HEq (coframeCast r h e) e := by
  subst h
  rfl

/- The right side of the exported comparison as one definition. Applications of a definition are
compared argument by argument, so the spellings of the chart and its base used by the comparison
and by the matching facts meet only as schemes. Under `Iso.hom` and `NatTrans.app`, which are
projections, the elaborator and the kernel instead unfold `pullbackComp` to compare them. -/
private def comparisonTail {P X Y Z : Scheme.{u}} (j : P ⟶ X) (q : X ⟶ Y) (z : Y ⟶ Z)
    {N : Y.Modules} (L : Z.Modules) (hN : N = (Scheme.Modules.pullback z).obj L)
    (e : (Scheme.Modules.pullback ((j ≫ q) ≫ z)).obj L ⟶ SheafOfModules.unit P.ringCatSheaf) :
    (Scheme.Modules.pullback q ⋙ Scheme.Modules.pullback j).obj N ⟶
      SheafOfModules.unit P.ringCatSheaf :=
  (Scheme.Modules.pullbackComp j q).hom.app N ≫ coframeCast (j ≫ q) hN.symm
    ((Scheme.Modules.pullbackComp (j ≫ q) z).hom.app L ≫ e)

/- A frame followed by a scalar, as one definition, for the same reason as `comparisonTail`:
the factor equation and the ratio meet here with the frame's base and module spelled differently,
and as a composition (a projection) the two sides would be compared by unfolding (75 s). -/
private def scaledFrame {P : Scheme.{u}} {M : P.Modules}
    (e : M ⟶ SheafOfModules.unit P.ringCatSheaf)
    (s : SheafOfModules.unit P.ringCatSheaf ⟶ SheafOfModules.unit P.ringCatSheaf) :
    M ⟶ SheafOfModules.unit P.ringCatSheaf :=
  e ≫ s

/- The ratio of the append and matching coframes, over arbitrary schemes. Each hypothesis is taken
exactly as its source states it: the matching evaluation `hm` on the leg `J'`, the comparison
`hf` with `W.symm.inv` and its right side as `comparisonTail`, the associativity congruence `hc`
and the factor equation `hs`. The two spellings of the leg and of the module are identified here
(`hJ`, `hN`), where it
is cheap; restating either fact in the other spelling makes the kernel evaluate the coframes at
the chart. -/
private theorem power_ratio {P X Y Z : Scheme.{u}} {M : X.Modules} {N : Y.Modules}
    {L : Z.Modules} {J J' : P ⟶ X} {q : X ⟶ Y} {z : Y ⟶ Z}
    {hN : N = (Scheme.Modules.pullback z).obj L} (W : (Scheme.Modules.pullback q).obj N ≅ M)
    {m : (Scheme.Modules.pullback J').obj M ⟶ SheafOfModules.unit P.ringCatSheaf}
    {f : (Scheme.Modules.pullback J).obj M ⟶ SheafOfModules.unit P.ringCatSheaf}
    {e₀ : (Scheme.Modules.pullback (J' ≫ q ≫ z)).obj L ⟶ SheafOfModules.unit P.ringCatSheaf}
    {e₁ : (Scheme.Modules.pullback (J ≫ q ≫ z)).obj L ⟶ SheafOfModules.unit P.ringCatSheaf}
    {em ef : (Scheme.Modules.pullback ((J ≫ q) ≫ z)).obj L ⟶
      SheafOfModules.unit P.ringCatSheaf}
    {s : SheafOfModules.unit P.ringCatSheaf ⟶ SheafOfModules.unit P.ringCatSheaf}
    (hm : HEq ((Scheme.Modules.pullback J').map W.hom ≫ m)
      ((Scheme.Modules.pullback J').map ((Scheme.Modules.pullbackComp q z).hom.app L) ≫
        (Scheme.Modules.pullbackComp J' (q ≫ z)).hom.app L ≫ e₀))
    (hc : (Scheme.Modules.pullbackCongr (Category.assoc J q z)).hom.app L ≫ e₁ = em)
    (hf : (Scheme.Modules.pullback J).map W.symm.inv ≫ f = comparisonTail J q z L hN ef)
    (hs : ef = scaledFrame em s) (hJ : J' = J) (he : HEq e₀ e₁) :
    HEq f (m ≫ s) := by
  unfold comparisonTail at hf
  unfold scaledFrame at hs
  subst hJ hN
  obtain rfl := eq_of_heq he
  have hm' := eq_of_heq hm
  have hassoc := associate_coframe J' q z L e₀ em hc
  have hf' := hf.trans (congrArg (fun t => (Scheme.Modules.pullbackComp J' q).hom.app
    ((Scheme.Modules.pullback z).obj L) ≫ t) (eq_of_heq (coframeCast_heq _ _ _)))
  rw [Iso.symm_inv] at hf'
  refine heq_of_eq ((cancel_epi ((Scheme.Modules.pullback J').map W.hom)).mp ?_)
  -- term proof: after the rewrites the goal is not type-correct at reducible transparency
  let A := (Scheme.Modules.pullbackComp J' q).hom.app ((Scheme.Modules.pullback z).obj L)
  let B := (Scheme.Modules.pullbackComp (J' ≫ q) z).hom.app L
  exact hf'.trans ((congrArg (fun t => A ≫ B ≫ t) hs).trans
    (((congrArg (fun t => A ≫ t) (Category.assoc B em s).symm).trans
      (Category.assoc A (B ≫ em) s).symm).trans
        ((congrArg (fun t => t ≫ s) (hassoc.symm.trans hm'.symm)).trans
          (Category.assoc _ m s))))

open private appendPolynomialLift appendPolynomialLift_endpoint
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoframes

private theorem endpoint_pullback {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {Y : Scheme.{u}}
    (P Q : Over (Spec (.of K))) (f : P ⟶ Q)
    (r : Q.left ⟶ Y) (z : Y ⟶ (flagVariety G).scheme) (v : P.left ⟶ Y)
    (h : f.left ≫ r = v) (a : Q ⟶ (reductiveVariety G).toOver)
    (ha : a.left ≫ SchubertGeometry.flagQuotient G = r ≫ z) :
    (f ≫ a).left ≫ SchubertGeometry.flagQuotient G = v ≫ z :=
  ((Category.assoc f.left a.left (SchubertGeometry.flagQuotient G)).trans
    (congrArg (fun x => f.left ≫ x) ha)).trans
      ((Category.assoc f.left r z).symm.trans (congrArg (fun x => x ≫ z) h))

private def comparisonResult {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (chi : G.characters) {X Y : Scheme.{u}}
    {P Q : Over (Spec (.of K))} (f : P ⟶ Q)
    {j : P.left ⟶ X} {q : X ⟶ Y} {k : P.left ⟶ Q.left} {r : Q.left ⟶ Y}
    (h : j ≫ q = k ≫ r) (h' : j ≫ q = f.left ≫ r)
    {M : X.Modules} {N : Y.Modules}
    (E : M ≅ (Scheme.Modules.pullback q).obj N)
    (e : (Scheme.Modules.pullback r).obj N ≅ SheafOfModules.unit Q.left.ringCatSheaf)
    (z : Y ⟶ (flagVariety G).scheme)
    (hN : N = (Scheme.Modules.pullback z).obj (CharacterLine.flagCharacterModule G chi))
    (a : Q ⟶ (reductiveVariety G).toOver)
    (ha : a.left ≫ SchubertGeometry.flagQuotient G = r ≫ z) : Prop :=
    (Scheme.Modules.pullback j).map E.inv ≫
        (comparisonCoframe j q k r h M N E e).hom =
      (Scheme.Modules.pullbackComp j q).hom.app N ≫ coframeCast (j ≫ q) hN.symm
        ((Scheme.Modules.pullbackComp (j ≫ q) z).hom.app
          (CharacterLine.flagCharacterModule G chi) ≫
            CharacterLine.characterFrameEvaluation G chi P ((j ≫ q) ≫ z) (f ≫ a)
              (endpoint_pullback G P Q f r z (j ≫ q) h'.symm a ha))

private theorem comparison_base_finish {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (chi : G.characters) {X Y : Scheme.{u}}
    {P Q : Over (Spec (.of K))} (f : P ⟶ Q)
    {j : P.left ⟶ X} {q : X ⟶ Y} {k : P.left ⟶ Q.left} {r : Q.left ⟶ Y}
    (h : j ≫ q = k ≫ r) (h' : j ≫ q = f.left ≫ r) (hleft : f.left = k)
    {M : X.Modules} {N : Y.Modules}
    (E : M ≅ (Scheme.Modules.pullback q).obj N)
    (e : (Scheme.Modules.pullback r).obj N ≅ SheafOfModules.unit Q.left.ringCatSheaf)
    (z : Y ⟶ (flagVariety G).scheme)
    (hN : N = (Scheme.Modules.pullback z).obj (CharacterLine.flagCharacterModule G chi))
    {e' : (Scheme.Modules.pullback r).obj
      ((Scheme.Modules.pullback z).obj (CharacterLine.flagCharacterModule G chi)) ⟶
        SheafOfModules.unit Q.left.ringCatSheaf}
    (he : HEq e.hom e')
    (a : Q ⟶ (reductiveVariety G).toOver)
    (ha : a.left ≫ SchubertGeometry.flagQuotient G = r ≫ z)
    (hR : HEq e' ((Scheme.Modules.pullbackComp r z).hom.app
      (CharacterLine.flagCharacterModule G chi) ≫
        CharacterLine.characterFrameEvaluation G chi Q (r ≫ z) a ha)) :
    comparisonResult G chi f h h' E e z hN a ha := by
  unfold comparisonResult
  cases hN
  cases hleft
  have hr : e' = (Scheme.Modules.pullbackComp r z).hom.app
      (CharacterLine.flagCharacterModule G chi) ≫
        CharacterLine.characterFrameEvaluation G chi Q (r ≫ z) a ha := eq_of_heq hR
  have hb := CoframeTransport.evaluation_base_change G chi Q P f r z (j ≫ q) h'.symm a ha
  exact comparison_finish h E e ((eq_of_heq he).trans hr) hb


private abbrev equalityRight {A : Sort u} {a b : A} (_h : a = b) : A := b

private abbrev evaluationMap {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (chi : G.characters) {Y : Scheme.{u}}
    (Q : Over (Spec (.of K))) (r : Q.left ⟶ Y)
    (z : Y ⟶ (flagVariety G).scheme)
    (a : Q ⟶ (reductiveVariety G).toOver)
    (ha : a.left ≫ SchubertGeometry.flagQuotient G = r ≫ z) :
    (Scheme.Modules.pullback r).obj
      ((Scheme.Modules.pullback z).obj (CharacterLine.flagCharacterModule G chi)) ⟶
      SheafOfModules.unit Q.left.ringCatSheaf :=
  (Scheme.Modules.pullbackComp r z).hom.app (CharacterLine.flagCharacterModule G chi) ≫
    CharacterLine.characterFrameEvaluation G chi Q (r ≫ z) a ha


private theorem comparison_export {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {G : ReductiveGroupData K} {chi : G.characters} {X Y : Scheme.{u}}
    {P Q : Over (Spec (.of K))} {f : P ⟶ Q}
    {j : P.left ⟶ X} {q : X ⟶ Y} {k : P.left ⟶ Q.left} {r : Q.left ⟶ Y}
    {h : j ≫ q = k ≫ r} {h' : j ≫ q = f.left ≫ r}
    {M : X.Modules} {N : Y.Modules}
    {E₀ : M ≅ (Scheme.Modules.pullback q).obj N}
    {e : (Scheme.Modules.pullback r).obj N ≅ SheafOfModules.unit Q.left.ringCatSheaf}
    {z : Y ⟶ (flagVariety G).scheme}
    {hN : N = (Scheme.Modules.pullback z).obj (CharacterLine.flagCharacterModule G chi)}
    {a : Q ⟶ (reductiveVariety G).toOver}
    {ha : a.left ≫ SchubertGeometry.flagQuotient G = r ≫ z}
    (hc : comparisonResult G chi f h h' E₀ e z hN a ha)
    (E : M ≅ (Scheme.Modules.pullback q).obj N) (hE : E₀ = E)
    (A : (Scheme.Modules.pullback j).obj M ≅ SheafOfModules.unit P.left.ringCatSheaf)
    (hA : A = comparisonCoframe j q k r h M N E e)
    (b : P ⟶ (reductiveVariety G).toOver) (hb : b = f ≫ a)
    (hquot : b.left ≫ SchubertGeometry.flagQuotient G = (j ≫ q) ≫ z) :
    (Scheme.Modules.pullback j).map E.inv ≫ A.hom =
      comparisonTail j q z (CharacterLine.flagCharacterModule G chi) hN
        (CharacterLine.characterFrameEvaluation G chi P ((j ≫ q) ≫ z) b hquot) := by
  cases hE
  cases hA
  cases hb
  exact hc

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K)

/- The chart lift `l` is any map equal to `a ≫ flagChartMap G g`, and the unit `u` any unit equal
to the Borel section, so that the caller passes both as its other facts spell them. The matching
lift is `map ≫ a' ≫ flagChartMap G g` while `a` is `map ≫ a'`; identifying the two associations
definitionally unfolds the scheme compositions down to their ring maps (120 s at the matching
chart). The unit is compared under the coercion of `ΓSpecIso`, a projection. -/
private theorem factor_power_at (A : CommAlgCat.{u} K) (g : G.points)
    (a : (algSpec (.of K)).obj (op A) ⟶ (oppositeUnipotentVariety G).toOver)
    (k : (algSpec (.of K)).obj (op A) ⟶ (reductiveVariety G).toOver)
    (h : a ≫ flagChartMorphism G g = k ≫ flagQuotientMorphism G)
    (m : Spec (.of A) ⟶ (flagVariety G).scheme)
    (hk : k.left ≫ SchubertGeometry.flagQuotient G = m)
    (l : (algSpec (.of K)).obj (op A) ⟶ (reductiveVariety G).toOver)
    (hl : l = a ≫ flagChartMap G g)
    (ha : l.left ≫ SchubertGeometry.flagQuotient G = m) (u : Aˣ)
    (hu : u = ProjectiveLine.positiveBorelSection G A (CharacterLine.frameBorelFactor G A g a k h))
    (n : ℕ) :
    CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (op A)) m k hk =
      scaledFrame (CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
        ((algSpec (.of K)).obj (op A)) m l ha)
      (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of A)).inv ((u : A) ^ n))) := by
  unfold scaledFrame
  subst hl hu
  have hr := CharacterLine.characterFrameEvaluation_rule G (G.positiveRootCharacter ^ n)
    ((algSpec (.of K)).obj (op A)) m k (a ≫ flagChartMap G g)
    (CharacterLine.frameBorelFactor G A g a k h) hk ha
    (CharacterLine.frameBorelFactor_mul G A g a k h)
  exact hr.trans (congrArg (fun t : Γ(Spec (.of A), ⊤) =>
    CharacterLine.characterFrameEvaluation G (G.positiveRootCharacter ^ n)
      ((algSpec (.of K)).obj (op A)) m (a ≫ flagChartMap G g) ha ≫
        Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec (.of A)).ringCatSheaf) t)
      (section_character_power G A (CharacterLine.frameBorelFactor G A g a k h) n))

section Append
variable (word : List G.rootBase.support) (i : G.rootBase.support) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (q : cF.pt.left ⟶ bsdhScheme G (word ++ [i]))
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G (word ++ [i])))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G F beta s j hj l hl =
      wordTransitionUnit G F beta s k hk l hl * wordTransitionUnit G F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (wordTransitionUnit G F beta s j hj k hk) =
        wordTransitionUnit G F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (s : {s : Finset J // s.Nonempty})
    (V : Over (Spec (.of K))) (g : G.points)
    (b : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (op B) ⟶ V)
    (j : Fin 2) (k : Spec (.of (F.obj s)) ⟶ Spec (.of (Polynomial B)))
    (hk : (cF.ι.app (op s)).left ≫ q =
      k ≫ projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c)

private abbrev chosenOpposite :
    (algSpec (.of K)).obj (op (F.obj s)) ⟶ (oppositeUnipotentVariety G).toOver :=
  (algSpec (.of K)).map
    (F.map (singletonArrow s s.property.choose s.property.choose_spec)).op ≫ a s.property.choose

omit hopen hdir in
include ha in
private theorem matching_local_quotient :
    (chartLift G F point a s s.property.choose s.property.choose_spec).left ≫
        SchubertGeometry.flagQuotient G =
      ((cF.ι.app (op s)).left ≫ q) ≫ bsdhMap G (word ++ [i]) :=
  (lift_quotient G F cF (word ++ [i]) q point a ha
    s s.property.choose s.property.choose_spec).trans
      ((Category.assoc (cF.ι.app (op s)).left q (bsdhMap G (word ++ [i]))).symm)

omit hopen hdir in
include ha hend hk in
private theorem append_endpoint :
    k ≫ (appendPolynomialLift G i V g b B p j).left ≫ SchubertGeometry.flagQuotient G =
      (chartLift G F point a s s.property.choose s.property.choose_spec).left ≫
        SchubertGeometry.flagQuotient G :=
  endpoint_factor
    (appendPolynomialLift G i V g b B p j).left
    (chartLift G F point a s s.property.choose s.property.choose_spec).left
    (SchubertGeometry.flagQuotient G) (cF.ι.app (op s)).left q k
    (projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c)
    (bsdhMap G (word ++ [i]))
    ((appendPolynomialLift_endpoint G word i V g b c hend B p j).trans
      (Category.assoc (projectiveLinePolynomialChart B ⟨j⟩)
        (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))).symm)
    (lift_quotient G F cF (word ++ [i]) q point a ha
      s s.property.choose s.property.choose_spec) hk

private def appendScalarFactor :
    (algSpec (.of K)).obj (op (F.obj s)) ⟶ polynomialBase B :=
  endpointMap k (appendPolynomialLift G i V g b B p j)
    (chartLift G F point a s s.property.choose s.property.choose_spec)
    (flagQuotientMorphism G)
    (append_endpoint G word i F cF q point a ha s V g b c hend B p j k hk)

private def appendLocalLift :
    (algSpec (.of K)).obj (op (F.obj s)) ⟶ (reductiveVariety G).toOver :=
  appendScalarFactor G word i F cF q point a ha s V g b c hend B p j k hk ≫
    appendPolynomialLift G i V g b B p j

omit hopen hdir in
private theorem append_local_quotient :
    (appendLocalLift G word i F cF q point a ha s V g b c hend B p j k hk).left ≫
        SchubertGeometry.flagQuotient G =
      ((cF.ι.app (op s)).left ≫ q) ≫ bsdhMap G (word ++ [i]) :=
  composite_quotient k (appendPolynomialLift G i V g b B p j).left
    (SchubertGeometry.flagQuotient G)
    (projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c)
    ((cF.ι.app (op s)).left ≫ q) (bsdhMap G (word ++ [i]))
    ((appendPolynomialLift_endpoint G word i V g b c hend B p j).trans
      (Category.assoc (projectiveLinePolynomialChart B ⟨j⟩)
        (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))).symm) hk.symm

include ha hk hend in
omit hopen hdir in
private theorem append_factor_endpoint :
    chosenOpposite G F a s ≫ flagChartMorphism G (point s.property.choose) =
      appendLocalLift G word i F cF q point a ha s V g b c hend B p j k hk ≫
        flagQuotientMorphism G := by
  apply CostructuredArrow.hom_ext
  have hcanonical : (chosenOpposite G F a s ≫ flagChartMap G (point s.property.choose)).left ≫
      SchubertGeometry.flagQuotient G =
      (chosenOpposite G F a s ≫ flagChartMorphism G (point s.property.choose)).left :=
    (Category.assoc _ _ _).trans
      (congrArg (fun x => (chosenOpposite G F a s).left ≫ x)
        (congrArg (fun f => f.left) (flagChartMap_quotient G (point s.property.choose))))
  exact hcanonical.symm.trans
    ((matching_local_quotient G word i F cF q point a ha s).trans
          (append_local_quotient G word i F cF q point a ha s V g b c hend B p j k hk).symm)

/-- The endpoint equation constructs one Borel unit comparing the append lift
with the selected matching lift on the specified intersection chart. -/
def appendBorelUnit : (F.obj s)ˣ :=
  ProjectiveLine.positiveBorelSection G (F.obj s)
    (CharacterLine.frameBorelFactor G (F.obj s) (point s.property.choose)
      (chosenOpposite G F a s)
      (appendLocalLift G word i F cF q point a ha s V g b c hend B p j k hk)
      (append_factor_endpoint G word i F cF q point a ha s V g b c hend B p j k hk))

/-- The polynomial append coframe transports to the same matching line for
each full character power on the specified chart factorization. -/
def appendPowerFrame (n : ℕ) :
    (Scheme.Modules.pullback (cF.ι.app (op s)).left).obj
      (matchingModule F cF (wordTransitionUnit G F beta) n) ≅
        SheafOfModules.unit (Spec (.of (F.obj s))).ringCatSheaf :=
  comparisonCoframe (cF.ι.app (op s)).left q k
    (projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c) hk
    (matchingModule F cF (wordTransitionUnit G F beta) n)
    (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
    (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q n point a ha beta hgroup hco hn).symm
    (appendPolynomialFrame G word i V g b c hend B p n ⟨j⟩)

omit hopen hdir in
include ha hend hk in
private theorem scalar_factor_left :
    (appendScalarFactor G word i F cF q point a ha s V g b c hend B p j k hk).left = k := rfl

omit hopen hdir in
include G word i F cF q point a ha s V g b c hend B p j k hk in
private theorem scalar_factorization : type_of% (
    factorization_arrow
      (scalar_factor_left G word i F cF q point a ha s V g b c hend B p j k hk) hk) := by
  have result := factorization_arrow
    (scalar_factor_left G word i F cF q point a ha s V g b c hend B p j k hk) hk
  exact result


omit hopen hdir in
include G word i V g b c hend B p in
private theorem eval_map_eq (n : ℕ) (j : Fin 2) :
    HEq (equalityRight (appendPolynomialFrame_evaluation G word i V g b c hend B p n j))
      (evaluationMap G (G.positiveRootCharacter ^ n)
        (Y := (Over.mk (bsdhToSpec G (word ++ [i]))).left)
        (polynomialBase B)
        (projectiveLinePolynomialChart B ⟨j⟩ ≫ projectiveAppendChart G i B p c)
        (bsdhMap G (word ++ [i]))
        (appendPolynomialLift G i V g b B p j)
        ((appendPolynomialLift_endpoint G word i V g b c hend B p j).trans
          (Category.assoc (projectiveLinePolynomialChart B ⟨j⟩)
            (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))).symm)) := by
  with_reducible exact HEq.rfl

private theorem exists_self_eq {A : Sort u} (a : A) : ∃ b : A, b = a := ⟨a, rfl⟩

include G word i F hopen hdir cF hcF q point a ha beta hgroup hco hn in
private theorem matchingComparison_exists (n : ℕ) : type_of% (
    exists_self_eq
      (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q n point a ha beta hgroup hco hn).symm
    ) := by
  exact exists_self_eq
    (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q n point a ha beta hgroup hco hn).symm

private noncomputable def matchingComparison (n : ℕ) :=
  Classical.choose (matchingComparison_exists G word i F cF hcF q point a ha beta hgroup hco hn n)

private theorem matchingComparison_spec (n : ℕ) :
    matchingComparison G word i F cF hcF q point a ha beta hgroup hco hn n =
      (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q n point a ha beta hgroup hco hn).symm :=
  Classical.choose_spec (matchingComparison_exists G word i F cF hcF q point a ha beta hgroup hco hn
      n)


include G word i F hopen hdir cF hcF q point a ha beta hgroup hco hn
  s V g b c hend B p j k hk in
private theorem complete_piece (n : ℕ) :
    comparisonResult G (G.positiveRootCharacter ^ n)
      (Y := (Over.mk (bsdhToSpec G (word ++ [i]))).left)
      (appendScalarFactor G word i F cF q point a ha s V g b c hend B p j k hk)
      hk
      (scalar_factorization G word i F cF q point a ha s V g b c hend B p j k hk)
      (matchingComparison G word i F cF hcF q point a ha beta hgroup hco hn n)
      (appendPolynomialFrame G word i V g b c hend B p n ⟨j⟩)
      (bsdhMap G (word ++ [i]))
      rfl
      (appendPolynomialLift G i V g b B p j)
      ((appendPolynomialLift_endpoint G word i V g b c hend B p j).trans
        (Category.assoc (projectiveLinePolynomialChart B ⟨j⟩)
          (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))).symm) := by
  have result := comparison_base_finish G (G.positiveRootCharacter ^ n)
    (Y := (Over.mk (bsdhToSpec G (word ++ [i]))).left)
    (appendScalarFactor G word i F cF q point a ha s V g b c hend B p j k hk)
    hk
    (scalar_factorization G word i F cF q point a ha s V g b c hend B p j k hk)
    (scalar_factor_left G word i F cF q point a ha s V g b c hend B p j k hk)
    (matchingComparison G word i F cF hcF q point a ha beta hgroup hco hn n)
    (appendPolynomialFrame G word i V g b c hend B p n ⟨j⟩)
    (bsdhMap G (word ++ [i]))
    rfl
    (heq_of_eq (appendPolynomialFrame_evaluation G word i V g b c hend B p n j))
    (appendPolynomialLift G i V g b B p j)
    ((appendPolynomialLift_endpoint G word i V g b c hend B p j).trans
      (Category.assoc (projectiveLinePolynomialChart B ⟨j⟩)
        (projectiveAppendChart G i B p c) (bsdhMap G (word ++ [i]))).symm)
    (by with_reducible exact eval_map_eq G word i V g b c hend B p n j)
  exact result

/-- A single constructed Borel unit gives the ratio of the polynomial append
and matching coframes for every full character power. -/
theorem appendPowerFrame_ratio (n : ℕ) :
    (appendPowerFrame G word i F cF hcF q point a ha beta hgroup hco hn
      s V g b c hend B p j k hk n).hom =
      (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn
        s s.property.choose s.property.choose_spec).hom ≫
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec (.of (F.obj s))).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of (F.obj s))).inv
          ((appendBorelUnit G word i F cF q point a ha s V g b c hend B p j k hk : F.obj s) ^ n)) :=
  eq_of_heq (power_ratio
    (N := CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
    (hN := rfl)
    (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q n point a ha beta hgroup hco hn)
    (heq_of_eq (wordMatchingFrame_evaluation G F cF hcF (word ++ [i]) q n point a ha
      beta hgroup hco hn s s.property.choose s.property.choose_spec))
    (CharacterLine.characterFrameEvaluation_congr G (G.positiveRootCharacter ^ n)
      ((algSpec (.of K)).obj (op (F.obj s)))
      (Category.assoc (cF.ι.app (op s)).left q (bsdhMap G (word ++ [i])))
      (chartLift G F point a s s.property.choose s.property.choose_spec)
      (matching_local_quotient G word i F cF q point a ha s))
    (comparison_export (Y := bsdhScheme G (word ++ [i]))
      (P := (F.op ⋙ algSpec (.of K)).obj (op s))
      (complete_piece G word i F cF hcF q point a ha beta hgroup hco hn s V g b c hend B p j k hk n)
      (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q n point a ha beta hgroup hco hn).symm
      (matchingComparison_spec G word i F cF hcF q point a ha beta hgroup hco hn n)
      (appendPowerFrame G word i F cF hcF q point a ha beta hgroup hco hn s V g b c hend B p j k hk
          n)
      rfl
      (appendLocalLift G word i F cF q point a ha s V g b c hend B p j k hk)
      rfl
      (append_local_quotient G word i F cF q point a ha s V g b c hend B p j k hk))
    (factor_power_at G (F.obj s) (point s.property.choose) (chosenOpposite G F a s)
      (appendLocalLift G word i F cF q point a ha s V g b c hend B p j k hk)
      (append_factor_endpoint G word i F cF q point a ha s V g b c hend B p j k hk)
      (((cF.ι.app (op s)).left ≫ q) ≫ bsdhMap G (word ++ [i]))
      (append_local_quotient G word i F cF q point a ha s V g b c hend B p j k hk)
      (chartLift G F point a s s.property.choose s.property.choose_spec)
      (Category.assoc _ _ _).symm
      (matching_local_quotient G word i F cF q point a ha s)
      (appendBorelUnit G word i F cF q point a ha s V g b c hend B p j k hk) rfl n)
    rfl HEq.rfl)

/-- The degree-one coframe ratio is the constructed Borel unit, so retaining
that ratio retains the scalar comparison for all character powers. -/
theorem appendFrameUnit_eq_borel :
    appendFrameUnit G word i F cF hcF q point a ha beta hgroup hco hn
      s V g b c hend B p ⟨j⟩ k hk =
      appendBorelUnit G word i F cF q point a ha s V g b c hend B p j k hk :=
  unit_ratio_from_power_one (F.obj s)
    (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) 1 hco hn
      s s.property.choose s.property.choose_spec)
    (appendPowerFrame G word i F cF hcF q point a ha beta hgroup hco hn
      s V g b c hend B p j k hk 1)
    (appendBorelUnit G word i F cF q point a ha s V g b c hend B p j k hk)
    (appendPowerFrame_ratio G word i F cF hcF q point a ha beta hgroup hco hn
      s V g b c hend B p j k hk 1)

/-- The retained degree-one ratio gives the scalar in every polynomial
append coframe power on the same intersection chart. -/
theorem appendPowerFrame_unit (n : ℕ) :
    (appendPowerFrame G word i F cF hcF q point a ha beta hgroup hco hn
      s V g b c hend B p j k hk n).hom =
      (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn
        s s.property.choose s.property.choose_spec).hom ≫
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec (.of (F.obj s))).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of (F.obj s))).inv
          ((appendFrameUnit G word i F cF hcF q point a ha beta hgroup hco hn
            s V g b c hend B p ⟨j⟩ k hk : F.obj s) ^ n)) := by
  exact (appendPowerFrame_ratio G word i F cF hcF q point a ha beta hgroup hco hn
    s V g b c hend B p j k hk n).trans
      (congrArg (fun u : (F.obj s)ˣ =>
        (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta) n hco hn
          s s.property.choose s.property.choose_spec).hom ≫
        Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec (.of (F.obj s))).ringCatSheaf)
          ((Scheme.ΓSpecIso (.of (F.obj s))).inv ((u : F.obj s) ^ n)))
        (appendFrameUnit_eq_borel G word i F cF hcF q point a ha beta hgroup hco hn
          s V g b c hend B p j k hk).symm)

end Append
end SchubertGeometry.RetainedCharacter
