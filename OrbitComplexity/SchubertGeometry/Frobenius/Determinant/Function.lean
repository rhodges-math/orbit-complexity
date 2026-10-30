import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.Power
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.Function
import OrbitComplexity.GroupActions.Varieties.AffineMultiplication

/-! # The regular determinant power as a full-character function -/

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions TauCeti WithConv
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

noncomputable section
universe u

namespace SchubertGeometry.DeterminantSection

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem groupSmooth : Algebra.Smooth K (G.coordinateAlgebra.obj : Type u) :=
  G.reductive.smooth

omit [CharZero K] in
private theorem borelSmooth : Algebra.Smooth K (G.borelAlgebra.obj : Type u) := G.borel_smooth

omit [IsAlgClosed K] [CharZero K] in
private theorem groupReduced : IsReduced (G.coordinateAlgebra.obj : Type u) := by
  let : Algebra.Smooth K (G.coordinateAlgebra.obj : Type u) := groupSmooth G
  exact isReduced_of_smooth K _

omit [CharZero K] in
private theorem borelReduced : IsReduced (G.borelAlgebra.obj : Type u) := by
  let : Algebra.Smooth K (G.borelAlgebra.obj : Type u) := borelSmooth G
  exact isReduced_of_smooth K _

omit [CharZero K] in
private theorem tensorSmooth :
    Algebra.Smooth K ((G.coordinateAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj) := by
  let : Algebra.Smooth K (G.coordinateAlgebra.obj : Type u) := groupSmooth G
  let : Algebra.Smooth K (G.borelAlgebra.obj : Type u) := borelSmooth G
  exact Algebra.Smooth.comp K (G.coordinateAlgebra.obj : Type u) _

omit [CharZero K] in
private theorem tensorReduced :
    IsReduced ((G.coordinateAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj) := by
  let : Algebra.Smooth K ((G.coordinateAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj) :=
    tensorSmooth G
  exact isReduced_of_smooth K _

omit [CharZero K] in
private theorem tensorFinite :
    Algebra.FiniteType K ((G.coordinateAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj) := by
  let : Algebra.Smooth K ((G.coordinateAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj) :=
    tensorSmooth G
  infer_instance

attribute [local instance] groupSmooth borelSmooth groupReduced borelReduced
  tensorReduced tensorFinite

private theorem spec_app {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      (Scheme.ΓSpecIso (.of B)).inv (f a) := by
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) a).symm

private def qB : G.coordinateAlgebra.obj →ₐ[K] G.borelAlgebra.obj :=
  ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom).toAlgHom

omit [CharZero K] in
private theorem tensor_right_mul :
    (affineTensorIso K (G.coordinateAlgebra.obj : Type u) G.borelAlgebra.obj).hom ≫
      (fst (reductiveVariety G).toOver (borelVariety G).toOver *
        (snd (reductiveVariety G).toOver (borelVariety G).toOver ≫ borelInclusion G)) =
    affineMorphism (affineMulMap (AlgHom.id K G.coordinateAlgebra.obj) (qB G)) := by
  let j : (affineVariety K (G.borelAlgebra.obj : Type u)).toOver ⟶ (affineVariety K
    (G.coordinateAlgebra.obj : Type u)).toOver := borelInclusion G
  change (affineTensorIso K (G.coordinateAlgebra.obj : Type u) G.borelAlgebra.obj).hom ≫
    (fst (affineVariety K (G.coordinateAlgebra.obj : Type u)).toOver (affineVariety K
      (G.borelAlgebra.obj : Type u)).toOver *
      (snd (affineVariety K (G.coordinateAlgebra.obj : Type u)).toOver (affineVariety K
        (G.borelAlgebra.obj : Type u)).toOver ≫ j)) = _

  let L : G.coordinateAlgebra.obj →ₐ[K]
      G.coordinateAlgebra.obj ⊗[K] G.borelAlgebra.obj := Algebra.TensorProduct.includeLeft
  let R : G.coordinateAlgebra.obj →ₐ[K]
      G.coordinateAlgebra.obj ⊗[K] G.borelAlgebra.obj :=
    Algebra.TensorProduct.includeRight.comp (qB G)
  have hL : (affineTensorIso K (G.coordinateAlgebra.obj : Type u) G.borelAlgebra.obj).hom ≫
      fst (affineVariety K (G.coordinateAlgebra.obj : Type u)).toOver (affineVariety K
        (G.borelAlgebra.obj : Type u)).toOver =
      Spec.mapMulEquiv (toConv L) := affineTensorIso_fst _ _ _
  have hR : (affineTensorIso K (G.coordinateAlgebra.obj : Type u) G.borelAlgebra.obj).hom ≫
      snd (affineVariety K (G.coordinateAlgebra.obj : Type u)).toOver (affineVariety K
        (G.borelAlgebra.obj : Type u)).toOver ≫ j =
      Spec.mapMulEquiv (toConv R) := by
    calc
      _ = ((affineTensorIso K (G.coordinateAlgebra.obj : Type u) G.borelAlgebra.obj).hom ≫
          snd (affineVariety K (G.coordinateAlgebra.obj : Type u)).toOver (affineVariety K
            (G.borelAlgebra.obj : Type u)).toOver) ≫
            j := (Category.assoc _ _ _).symm
      _ = affineMorphism (Algebra.TensorProduct.includeRight : G.borelAlgebra.obj →ₐ[K]
          G.coordinateAlgebra.obj ⊗[K] G.borelAlgebra.obj) ≫ j :=
        congrArg (fun f => f ≫ j)
          (affineTensorIso_snd K (G.coordinateAlgebra.obj : Type u) G.borelAlgebra.obj)
      _ = _ := by
        apply Over.OverMorphism.ext
        change Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : G.borelAlgebra.obj →ₐ[K]
              G.coordinateAlgebra.obj ⊗[K] G.borelAlgebra.obj).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (qB G).toRingHom) =
          Spec.map (CommRingCat.ofHom R.toRingHom)
        rw [← Spec.map_comp]
        rfl
  have hconv : (toConv L * toConv R).ofConv =
      affineMulMap (AlgHom.id K G.coordinateAlgebra.obj) (qB G) := by
    rw [AlgHom.convMul_def]
    change (Algebra.TensorProduct.lmul' K).comp
        ((Algebra.TensorProduct.map L R).comp
          (Bialgebra.comulAlgHom K G.coordinateAlgebra.obj)) = _
    have hm : (Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map L R) =
        Algebra.TensorProduct.map (AlgHom.id K G.coordinateAlgebra.obj) (qB G) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      change (a ⊗ₜ[K] 1) * (1 ⊗ₜ[K] qB G b) = a ⊗ₜ[K] qB G b
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [← AlgHom.comp_assoc, hm]
    rfl
  let T := (affineVariety K ((G.coordinateAlgebra.obj : Type u) ⊗[K]
    G.borelAlgebra.obj)).toOver
  let H := (affineVariety K (G.coordinateAlgebra.obj : Type u)).toOver
  let a : T ⟶ H := Spec.mapMulEquiv (toConv L)
  let b : T ⟶ H := Spec.mapMulEquiv (toConv R)
  have hab : a * b = (Spec.mapMulEquiv (toConv L * toConv R) : T ⟶ H) :=
    (map_mul Spec.mapMulEquiv (toConv L) (toConv R)).symm
  have hc : (Spec.mapMulEquiv (toConv L * toConv R) : T ⟶ H) =
      (affineMorphism (affineMulMap (AlgHom.id K G.coordinateAlgebra.obj) (qB G)) : T ⟶ H) :=
    congrArg (fun (f : G.coordinateAlgebra.obj →ₐ[K]
      G.coordinateAlgebra.obj ⊗[K] G.borelAlgebra.obj) =>
        (affineMorphism f : T ⟶ H)) hconv
  have hproduct :
      (affineTensorIso K (G.coordinateAlgebra.obj : Type u) G.borelAlgebra.obj).hom ≫
        (fst (affineVariety K (G.coordinateAlgebra.obj : Type u)).toOver (affineVariety K
          (G.borelAlgebra.obj : Type u)).toOver *
          (snd (affineVariety K (G.coordinateAlgebra.obj : Type u)).toOver (affineVariety K
            (G.borelAlgebra.obj : Type u)).toOver ≫ j)) =
      (a * b : T ⟶ H) := by
    rw [MonObj.comp_mul, hL, hR]
  exact hproduct.trans (hab.trans hc)

/-- The original determinant power regarded as a global regular function on the group. -/
def positiveDetPowerFunction (N : ℕ) : Γ((reductiveVariety G).scheme, ⊤) :=
  (Scheme.ΓSpecIso (.of (G.coordinateAlgebra.obj : Type u))).inv (positiveDetPower G N)

/-- The same global function has its full right Borel character as a regular function equality. -/
theorem positiveDetPowerFunction_right (N : ℕ) :
    (fst (reductiveVariety G).toOver (borelVariety G).toOver *
        (snd (reductiveVariety G).toOver (borelVariety G).toOver ≫ borelInclusion G)).left.appTop
        (positiveDetPowerFunction G N) =
      (fst (reductiveVariety G).toOver (borelVariety G).toOver).left.appTop
          (positiveDetPowerFunction G N) *
        (snd (reductiveVariety G).toOver (borelVariety G).toOver).left.appTop
          (CharacterLine.borelCharacterSection G (G.positiveRootCharacter ^ N)) := by
  let e := affineTensorIso K (G.coordinateAlgebra.obj : Type u) G.borelAlgebra.obj
  let es := (Over.forget (Spec (CommRingCat.of K))).mapIso e
  let eg : Γ(((reductiveVariety G).toOver ⊗ (borelVariety G).toOver).left, ⊤) ≅
      Γ((affineVariety K ((G.coordinateAlgebra.obj : Type u) ⊗[K]
        G.borelAlgebra.obj)).scheme, ⊤) := Scheme.Γ.mapIso es.op
  let phi : Γ(((reductiveVariety G).toOver ⊗ (borelVariety G).toOver).left, ⊤) →+*
      Γ((affineVariety K ((G.coordinateAlgebra.obj : Type u) ⊗[K]
        G.borelAlgebra.obj)).scheme, ⊤) := eg.hom.hom
  have hphi : Function.Injective phi := eg.commRingCatIsoToRingEquiv.injective
  apply hphi
  rw [map_mul phi]
  let evaluateG :
      ((affineVariety K ((G.coordinateAlgebra.obj : Type u) ⊗[K]
        G.borelAlgebra.obj)).toOver ⟶ (reductiveVariety G).toOver) →
      Γ((affineVariety K ((G.coordinateAlgebra.obj : Type u) ⊗[K]
        G.borelAlgebra.obj)).scheme, ⊤) :=
    fun f => f.left.appTop (positiveDetPowerFunction G N)
  let evaluateB :
      ((affineVariety K ((G.coordinateAlgebra.obj : Type u) ⊗[K]
        G.borelAlgebra.obj)).toOver ⟶ (borelVariety G).toOver) →
      Γ((affineVariety K ((G.coordinateAlgebra.obj : Type u) ⊗[K]
        G.borelAlgebra.obj)).scheme, ⊤) :=
    fun f => f.left.appTop
      (CharacterLine.borelCharacterSection G (G.positiveRootCharacter ^ N))
  have hm := congrArg evaluateG (tensor_right_mul G)
  have hf := congrArg evaluateG
    (affineTensorIso_fst K (G.coordinateAlgebra.obj : Type u) G.borelAlgebra.obj)
  have hs := congrArg evaluateB
    (affineTensorIso_snd K (G.coordinateAlgebra.obj : Type u) G.borelAlgebra.obj)
  have ht : evaluateG
      (affineMorphism (affineMulMap (AlgHom.id K G.coordinateAlgebra.obj) (qB G))) =
      evaluateG (affineMorphism (Algebra.TensorProduct.includeLeft :
        G.coordinateAlgebra.obj →ₐ[K] G.coordinateAlgebra.obj ⊗[K] G.borelAlgebra.obj)) *
      evaluateB (affineMorphism (Algebra.TensorProduct.includeRight :
        G.borelAlgebra.obj →ₐ[K] G.coordinateAlgebra.obj ⊗[K] G.borelAlgebra.obj)) := by
    change (Spec.map (CommRingCat.ofHom
      (affineMulMap (AlgHom.id K G.coordinateAlgebra.obj) (qB G)).toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (G.coordinateAlgebra.obj : Type u))).inv _) =
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
      G.coordinateAlgebra.obj →ₐ[K] G.coordinateAlgebra.obj ⊗[K]
        G.borelAlgebra.obj).toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (G.coordinateAlgebra.obj : Type u))).inv _) *
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        G.borelAlgebra.obj →ₐ[K] G.coordinateAlgebra.obj ⊗[K] G.borelAlgebra.obj).toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (G.borelAlgebra.obj : Type u))).inv _)
    rw [spec_app, spec_app, spec_app]
    have hc : affineMulMap (AlgHom.id K G.coordinateAlgebra.obj) (qB G)
        (positiveDetPower G N) =
        (Algebra.TensorProduct.includeLeft : G.coordinateAlgebra.obj →ₐ[K]
          G.coordinateAlgebra.obj ⊗[K] G.borelAlgebra.obj) (positiveDetPower G N) *
        (Algebra.TensorProduct.includeRight : G.borelAlgebra.obj →ₐ[K]
          G.coordinateAlgebra.obj ⊗[K] G.borelAlgebra.obj)
            (borelCharacterMap G (G.positiveRootCharacter ^ N)
              (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) := by
      change (Algebra.TensorProduct.map (AlgHom.id K G.coordinateAlgebra)
        ((CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom).toAlgHom)
          (Bialgebra.comulAlgHom K G.coordinateAlgebra (positiveDetPower G N)) = _
      rw [positiveDetPower_right_coaction]
      simp only [Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one]
      rfl
    exact (congrArg (Scheme.ΓSpecIso (.of ((G.coordinateAlgebra.obj : Type u) ⊗[K]
      G.borelAlgebra.obj))).inv hc).trans
        (map_mul (Scheme.ΓSpecIso (.of ((G.coordinateAlgebra.obj : Type u) ⊗[K]
          G.borelAlgebra.obj))).inv.hom _ _)
  exact hm.trans (ht.trans (congrArg₂ (· * ·) hf.symm hs.symm))

end SchubertGeometry.DeterminantSection
