import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendBorelCharts
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonMatchingCoframes
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Retaining matching coframes in Borel append charts

The original line and Borel charts are carried through the common affine cover.
Their frame ratios are retained at one coefficient extension.
-/

set_option autoImplicit false
set_option pp.maxSteps 1000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct

namespace SchubertGeometry

open RetainedCharacter

universe u

open private singletonIndex from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private initialCoefficient finalCoefficient polynomialSpecMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendScalarComparisons
open private borelPolynomialLeg borel_polynomial_base from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendBorelCharts

private def chartThroughIso {A B C : Scheme.{u}} (f : A ⟶ B) (E : C ≅ B) :
    A ⟶ C := f ≫ E.inv

section Retention

variable {K S T I : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    [sComm : CommRing S] [tComm : CommRing T] (R : Subalgebra ℤ K)
    [sTAlg : Algebra S T] [tRAlg : Algebra T R]
    [sKAlg : Algebra S K] [tKAlg : Algebra T K]
    [sTK : IsScalarTower S T K] [tRK : IsScalarTower T R K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support)
    (F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K)
    (N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S)
    (e : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s)
    (sel : ∀ s : {s : Finset I // s.Nonempty}, {j // j ∈ s.val})
    (V₀ : I → Over (Spec (.of K)))
    (p : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ V₀ j)
    (c : ∀ j, V₀ j ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))


variable {J : Type u} [jFinite : Finite J]
    (MN : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (MN.map f).hom.toRingHom))]
    [hNdir : ((MN.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (MN.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    [hNSep : cN.pt.left.IsSeparated] [hNSmooth : Smooth cN.pt.hom]
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (MN.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hnat : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (MN.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (g : I → G.points)
    (a₀ : ∀ j, V₀ j ⟶ (oppositeUnipotentVariety G).toOver)
    (hend : ∀ j, (c j).left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a₀ j ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ (g j))

variable (D : {s : Finset I // s.Nonempty}ᵒᵖ ⥤ Scheme.{u})
    (eP : ∀ s, D.obj (op s) ≅ projectiveScheme (N.obj s) (ULift.{u} (Fin 2)))
    (cD : Cocone D) (hOpen : ∀ s, IsOpenImmersion (cD.ι.app s))
    (hCover : ∀ (Z : Scheme.{u}) (f : Z ⟶ cD.pt) (z : Z),
      ∃ s, ∃ x : (pullback f (cD.ι.app s) : Scheme.{u}),
        pullback.fst f (cD.ι.app s) x = z)
    (base : cD.pt ⟶ Spec (.of S))
    (m : bsdhScheme G (word ++ [i]) ⟶ cD.pt)
    (h₀ : IsPullback m (bsdhToSpec G (word ++ [i])) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (b : ∀ s, Spec (.of (F.obj s)) ⟶ bsdhScheme G word)
    (hbbase : ∀ s, b s ≫ bsdhToSpec G word =
      Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))))
    (hfield : ∀ s j, borelPolynomialLeg G word i F sel V₀ p c s j ≫ m =
      polynomialSpecMap (initialCoefficient (e s)) ≫
        (projectiveLinePolynomialChart (N.obj s) j ≫ (eP s).inv ≫ cD.ι.app (op s)))
    (hprior : ∀ s j, borelPolynomialLeg G word i F sel V₀ p c s j ≫
      bsdhAppendFst G word i =
        Spec.map (CommRingCat.ofHom (Polynomial.C : F.obj s →+* Polynomial (F.obj s))) ≫ b s)

variable {Y Z : Scheme.{u}}
    (baseK : Z ⟶ Spec (.of K))
    (E : Z ≅ bsdhScheme G (word ++ [i]))
    (r : Z ⟶ bsdhScheme G (word ++ [i])) (hEr : E.hom = r)
    (hE : E.hom ≫ bsdhToSpec G (word ++ [i]) = baseK)
    (q₁ : Y ⟶ cD.pt) (q₂ : cN.pt.left ⟶ Y)
    (n : Z ⟶ cN.pt.left) (m₁ : bsdhScheme G (word ++ [i]) ⟶ Y)
    (hn : n ≫ q₂ = E.hom ≫ m₁) (hm : m₁ ≫ q₁ = m)
    (hK : IsPullback n baseK cN.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (V₁ : Y.OpenCover.{u})
    (index₁ : V₁.I₀ ≃ (appendPolynomialCover N D eP cD hOpen hCover).I₀)
    (eV₁ : ∀ j, V₁.X j ≅
      Spec (.of (Polynomial (T ⊗[S] N.obj (index₁ j).1))))
    (hV₁ : ∀ j, V₁.f j ≫ q₁ = (eV₁ j).hom ≫
      polynomialSpecMap (Algebra.TensorProduct.includeRight :
        N.obj (index₁ j).1 →ₐ[S] T ⊗[S] N.obj (index₁ j).1).toRingHom ≫
          (appendPolynomialCover N D eP cD hOpen hCover).f (index₁ j))
    (V : cN.pt.left.OpenCover.{u}) (index₂ : V.I₀ ≃ V₁.I₀)
    (eV : ∀ j, V.X j ≅
      Spec (.of (Polynomial (R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ j)).1)))))
    (hV : ∀ j, V.f j ≫ q₂ = (eV j).hom ≫
      polynomialSpecMap (Algebra.TensorProduct.includeRight :
        T ⊗[S] N.obj (index₁ (index₂ j)).1 →ₐ[T]
          R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ j)).1)).toRingHom ≫
            (eV₁ (index₂ j)).inv ≫ V₁.f (index₂ j))
    (hVbase : ∀ j, V.f j ≫ cN.pt.hom = (eV j).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Polynomial (R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ j)).1))))))
    [vFinite : Finite V.I₀] [vAffine : ∀ j, IsAffine (V.X j)]
    (EL : (Scheme.Modules.pullback n).obj
        (matchingModule MN cN delta 1) ≅
      (Scheme.Modules.pullback r).obj
        (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) (word ++ [i])))


/-- Polynomial field charts retain their Cartesian, word, coefficient and base equations
together with the coframes on the matching line. -/
def appendMatchingRetentionData (Q : Subalgebra ℤ K) (hRQ : R ≤ Q) : Prop :=
  ∃ (πField : ∀ v : V.I₀,
      Spec (.of (Polynomial (F.obj (index₁ (index₂ v)).1))) ⟶ V.X v)
    (jK : ∀ v : V.I₀,
      Spec (.of (Polynomial (F.obj (index₁ (index₂ v)).1))) ⟶ Z),
  (∀ v, IsPullback (πField v) (jK v) (V.f v) n) ∧
  (∀ v, jK v ≫ r = @borelPolynomialLeg.{u} K I kField kClosed kZero G word i F sel V₀ p c (index₁
      (index₂ v)).1 (index₁ (index₂ v)).2) ∧
  (∀ v, πField v = (@polynomialSpecMap.{u} (R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ v)).1)) (F.obj
      (index₁ (index₂ v)).1)
      (inferInstanceAs (CommRing (R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ v)).1))))
      (@CommAlgCat.commRing K (@Field.toCommRing K kField) (F.obj (index₁ (index₂ v)).1))
          (@finalCoefficient.{u} S T R K (N.obj (index₁ (index₂ v)).1) (F.obj (index₁ (index₂ v)).1)
      sComm tComm (inferInstanceAs (CommRing R)) (@Field.toCommRing K kField)
      (@CommAlgCat.commRing S sComm (N.obj (index₁ (index₂ v)).1))
      (@CommAlgCat.commRing K (@Field.toCommRing K kField) (F.obj (index₁ (index₂ v)).1))
      sTAlg tRAlg sKAlg tKAlg (inferInstanceAs (Algebra R K)) sTK tRK
      (@CommAlgCat.algebra S sComm (N.obj (index₁ (index₂ v)).1))
      (@CommAlgCat.algebra K (@Field.toCommRing K kField) (F.obj (index₁ (index₂ v)).1)) (e (index₁
          (index₂ v)).1))) ≫ (eV v).inv) ∧
  (∀ v, jK v ≫ baseK = Spec.map (CommRingCat.ofHom
    (algebraMap K (Polynomial (F.obj (index₁ (index₂ v)).1))))) ∧
  @commonMatchingCoframeData.{u} K kField kClosed kZero G word i R J jFinite MN
    (@hNopen) hNdir cN hcN hNSep delta hco hnat Z baseK n hK r EL V vAffine
    (fun v => V₀ (sel (index₁ (index₂ v)).1).val)
    (fun v => g (sel (index₁ (index₂ v)).1).val)
    (fun v => a₀ (sel (index₁ (index₂ v)).1).val)
    (fun v => c (sel (index₁ (index₂ v)).1).val)
    (fun v => hend (sel (index₁ (index₂ v)).1).val)
    (fun v => F.obj (index₁ (index₂ v)).1)
    (fun v => p (index₁ (index₂ v)).1
      (sel (index₁ (index₂ v)).1).val (sel (index₁ (index₂ v)).1).property)
    (fun v => (index₁ (index₂ v)).2)
    πField
    jK
    Q hRQ

omit [Smooth cN.pt.hom] in
/-- Construct the field-chart comparisons and retain their matching coframes once. -/
theorem exists_append_matching_retention
    (h₀ : IsPullback m (bsdhToSpec G (word ++ [i])) base
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hbbase : ∀ s, b s ≫ bsdhToSpec G word =
      Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s))))
    (hfield : ∀ s j, borelPolynomialLeg G word i F sel V₀ p c s j ≫ m =
      polynomialSpecMap (initialCoefficient (e s)) ≫
        (projectiveLinePolynomialChart (N.obj s) j ≫ (eP s).inv ≫ cD.ι.app (op s)))
    (hprior : ∀ s j, borelPolynomialLeg G word i F sel V₀ p c s j ≫
      bsdhAppendFst G word i =
        Spec.map (CommRingCat.ofHom (Polynomial.C : F.obj s →+* Polynomial (F.obj s))) ≫ b s)
    (hEr : E.hom = r)
    (hE : E.hom ≫ bsdhToSpec G (word ++ [i]) = baseK)
    (hn : n ≫ q₂ = E.hom ≫ m₁)
    (hm : m₁ ≫ q₁ = m)
    (hV₁ : ∀ j, V₁.f j ≫ q₁ = (eV₁ j).hom ≫
      polynomialSpecMap (Algebra.TensorProduct.includeRight :
        N.obj (index₁ j).1 →ₐ[S] T ⊗[S] N.obj (index₁ j).1).toRingHom ≫
          (appendPolynomialCover N D eP cD hOpen hCover).f (index₁ j))
    (hV : ∀ j, V.f j ≫ q₂ = (eV j).hom ≫
      polynomialSpecMap (Algebra.TensorProduct.includeRight :
        T ⊗[S] N.obj (index₁ (index₂ j)).1 →ₐ[T]
          R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ j)).1)).toRingHom ≫
            (eV₁ (index₂ j)).inv ≫ V₁.f (index₂ j))
    (hVbase : ∀ j, V.f j ≫ cN.pt.hom = (eV j).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Polynomial (R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ j)).1))))))
    (hNSmooth : Smooth cN.pt.hom) (hR : R.FG) :
    ∃ (Q : Subalgebra ℤ K) (hRQ : R ≤ Q), Q.FG ∧
      @appendMatchingRetentionData.{u} K S T I kField kClosed kZero sComm tComm R
        sTAlg tRAlg sKAlg tKAlg sTK tRK G word i F N e sel V₀ p c J jFinite MN
        (@hNopen) hNdir cN hcN hNSep delta hco hnat g a₀ hend D eP cD hOpen hCover
        Y Z baseK r n hK V₁ index₁ V index₂ eV vAffine EL Q hRQ := by
  let W := matchingSingletonCover MN cN hcN
  let : Finite W.I₀ := inferInstanceAs (Finite J)
  let : ∀ w, IsAffine (W.X w) := fun w =>
    inferInstanceAs (IsAffine (Spec (.of (MN.obj (singletonIndex w)))))
  have hcharts := @append_borel_matching_charts.{u} K S T R I
    kField kClosed kZero sComm tComm (inferInstanceAs (CommRing R))
    sTAlg tRAlg sKAlg tKAlg (inferInstanceAs (Algebra R K)) sTK tRK
    G word i F N e sel V₀ p c D eP cD hOpen hCover base m h₀ b hbbase hfield hprior
    Y cN.pt.left Z cN.pt.hom baseK E r hEr hE q₁ q₂ n m₁ hn hm hK
    V₁ index₁ eV₁ hV₁ V index₂ eV hV hVbase hNSep hNSmooth W
    (inferInstanceAs (Finite W.I₀)) vFinite
    (inferInstanceAs (∀ w, IsAffine (W.X w))) vAffine Subtype.val_injective
  obtain ⟨hword, _hsm, _hWfinite, _hVfinite, hcart, hcoords⟩ := hcharts
  obtain ⟨Q, hRQ, hQ, hdata⟩ := @exists_common_matching_coframes.{u}
    K kField kClosed kZero G word i R J jFinite MN (@hNopen) hNdir cN hcN hNSep hNSmooth
    delta hco hnat Z baseK n hK r EL V vAffine
    (fun v => V₀ (sel (index₁ (index₂ v)).1).val)
    (fun v => g (sel (index₁ (index₂ v)).1).val)
    (fun v => a₀ (sel (index₁ (index₂ v)).1).val)
    (fun v => c (sel (index₁ (index₂ v)).1).val)
    (fun v => hend (sel (index₁ (index₂ v)).1).val)
    (fun v => F.obj (index₁ (index₂ v)).1)
    (fun v => p (index₁ (index₂ v)).1
      (sel (index₁ (index₂ v)).1).val (sel (index₁ (index₂ v)).1).property)
    (fun v => (index₁ (index₂ v)).2)
    (fun v => @chartThroughIso.{u} (Spec (.of (Polynomial (F.obj (index₁ (index₂ v)).1))))
      (Spec (.of (Polynomial (R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ v)).1))))) (V.X v)
      (@polynomialSpecMap.{u} (R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ v)).1)) (F.obj (index₁ (index₂
          v)).1)
      (inferInstanceAs (CommRing (R ⊗[T] (T ⊗[S] N.obj (index₁ (index₂ v)).1))))
      (@CommAlgCat.commRing K (@Field.toCommRing K kField) (F.obj (index₁ (index₂ v)).1))
          (@finalCoefficient.{u} S T R K (N.obj (index₁ (index₂ v)).1) (F.obj (index₁ (index₂ v)).1)
      sComm tComm (inferInstanceAs (CommRing R)) (@Field.toCommRing K kField)
      (@CommAlgCat.commRing S sComm (N.obj (index₁ (index₂ v)).1))
      (@CommAlgCat.commRing K (@Field.toCommRing K kField) (F.obj (index₁ (index₂ v)).1))
      sTAlg tRAlg sKAlg tKAlg (inferInstanceAs (Algebra R K)) sTK tRK
      (@CommAlgCat.algebra S sComm (N.obj (index₁ (index₂ v)).1))
      (@CommAlgCat.algebra K (@Field.toCommRing K kField) (F.obj (index₁ (index₂ v)).1)) (e (index₁
          (index₂ v)).1))) (eV v))
    (fun v => @chartThroughIso.{u} (Spec (.of (Polynomial (F.obj (index₁ (index₂ v)).1))))
      (bsdhScheme G (word ++ [i])) Z (@borelPolynomialLeg.{u} K I kField kClosed kZero G word i F
          sel V₀ p c (index₁ (index₂ v)).1 (index₁ (index₂ v)).2) E)
    (fun v => hword (index₁ (index₂ v))) hR hcoords

  refine ⟨Q, hRQ, hQ, ?_⟩
  dsimp only [appendMatchingRetentionData]
  refine ⟨_, _, hcart, (fun v => hword (index₁ (index₂ v))), (fun _ => rfl), ?_, hdata⟩
  intro v
  dsimp only [chartThroughIso]
  rw [← hE]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    (@borel_polynomial_base.{u} K I kField kClosed kZero G word i F sel V₀ p c b hbbase hprior
      (index₁ (index₂ v)).1 (index₁ (index₂ v)).2)

end Retention

end SchubertGeometry
