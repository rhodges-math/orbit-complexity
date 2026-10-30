import OrbitComplexity.SchubertGeometry.LineBundles.Characters.CharacterLine
import OrbitComplexity.GroupActions.Varieties.AffineTensorProduct

/-! # Regular character functions on Borel-valued morphisms -/

open AlgebraicGeometry CategoryTheory ReductiveGroups GroupActions TauCeti
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

noncomputable section
universe u

namespace SchubertGeometry.CharacterLine

private theorem spec_app {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      (Scheme.ΓSpecIso (.of B)).inv (f a) := by
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) a).symm

private theorem groupLike_tensor {K A : Type u} [Field K] [CommRing A]
    [Bialgebra K A] (c : A) (hc : IsGroupLikeElem K c) :
    (Bialgebra.comulAlgHom K A) c =
      (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A) c *
        (Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A) c := by
  change Coalgebra.comul c = _
  rw [hc.comul_eq_tmul_self]
  simp only [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one]

private theorem pull_multiplicative {S : Scheme.{u}} (H : Over S) [MonObj H]
    (c : Γ(H.left, ⊤))
    (hc : (fst H H * snd H H).left.appTop c =
      (fst H H).left.appTop c * (snd H H).left.appTop c)
    (X : Over S) (f g : X ⟶ H) :
    (f * g).left.appTop c = f.left.appTop c * g.left.appTop c := by
  let phi : Γ((H ⊗ H).left, ⊤) →+* Γ(X.left, ⊤) := (lift f g).left.appTop.hom
  have h := (congrArg phi hc).trans
    (map_mul phi ((fst H H).left.appTop c) ((snd H H).left.appTop c))
  change ((lift f g ≫ (fst H H * snd H H)).left.appTop) c =
    ((lift f g ≫ fst H H).left.appTop) c *
      ((lift f g ≫ snd H H).left.appTop) c at h
  simpa only [MonObj.comp_mul, lift_fst, lift_snd] using h

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

omit [CharZero K] in
private theorem borelSmooth : Algebra.Smooth K (G.borelAlgebra.obj : Type u) :=
  G.borel_smooth

omit [CharZero K] in
private theorem borelReduced : IsReduced (G.borelAlgebra.obj : Type u) := by
  let : Algebra.Smooth K (G.borelAlgebra.obj : Type u) := borelSmooth G
  exact isReduced_of_smooth K (G.borelAlgebra.obj : Type u)

omit [CharZero K] in
private theorem tensorSmooth :
    Algebra.Smooth K ((G.borelAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj) := by
  let : Algebra.Smooth K (G.borelAlgebra.obj : Type u) := borelSmooth G
  exact Algebra.Smooth.comp K (G.borelAlgebra.obj : Type u) _

omit [CharZero K] in
private theorem tensorReduced :
    IsReduced ((G.borelAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj) := by
  let : Algebra.Smooth K ((G.borelAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj) :=
    tensorSmooth G
  exact isReduced_of_smooth K _

omit [CharZero K] in
private theorem tensorFinite :
    Algebra.FiniteType K ((G.borelAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj) := by
  let : Algebra.Smooth K ((G.borelAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj) :=
    tensorSmooth G
  infer_instance

attribute [local instance] borelSmooth borelReduced tensorReduced tensorFinite

/-- The global regular function of the specified full Borel character. -/
def borelCharacterSection (chi : G.characters) : Γ((borelVariety G).scheme, ⊤) :=
  (Scheme.ΓSpecIso (.of (G.borelAlgebra.obj : Type u))).inv
    (borelCharacterMap G chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1))

omit [CharZero K] in
private theorem tensor_mul :
    (affineTensorIso K (G.borelAlgebra.obj : Type u) G.borelAlgebra.obj).hom ≫
        (fst (borelVariety G).toOver (borelVariety G).toOver *
          snd (borelVariety G).toOver (borelVariety G).toOver) =
      affineMorphism (Bialgebra.comulAlgHom K (G.borelAlgebra.obj : Type u)) := by
  have hm : fst (borelVariety G).toOver (borelVariety G).toOver *
      snd (borelVariety G).toOver (borelVariety G).toOver =
      μ[(borelVariety G).toOver] := by
    change lift (fst _ _) (snd _ _) ≫ μ[(borelVariety G).toOver] = _
    rw [lift_fst_snd, Category.id_comp]
  rw [hm]
  apply Over.OverMorphism.ext
  change (pullbackSpecIso K (G.borelAlgebra.obj : Type u) G.borelAlgebra.obj).inv ≫
      ((pullbackSpecIso K (G.borelAlgebra.obj : Type u) G.borelAlgebra.obj).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom K
          (G.borelAlgebra.obj : Type u)).toRingHom)) = _
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rfl

private theorem character_mul_universal (chi : G.characters) :
    (fst (borelVariety G).toOver (borelVariety G).toOver *
        snd (borelVariety G).toOver (borelVariety G).toOver).left.appTop
        (borelCharacterSection G chi) =
      (fst (borelVariety G).toOver (borelVariety G).toOver).left.appTop
          (borelCharacterSection G chi) *
        (snd (borelVariety G).toOver (borelVariety G).toOver).left.appTop
          (borelCharacterSection G chi) := by
  let e := affineTensorIso K (G.borelAlgebra.obj : Type u) G.borelAlgebra.obj
  let es := (Over.forget (Spec (CommRingCat.of K))).mapIso e
  let eg : Γ(((borelVariety G).toOver ⊗ (borelVariety G).toOver).left, ⊤) ≅
      Γ((affineVariety K ((G.borelAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj)).scheme, ⊤) :=
    Scheme.Γ.mapIso es.op
  let phi : Γ(((borelVariety G).toOver ⊗ (borelVariety G).toOver).left, ⊤) →+*
      Γ((affineVariety K ((G.borelAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj)).scheme, ⊤) :=
    eg.hom.hom
  have hphi : Function.Injective phi := eg.commRingCatIsoToRingEquiv.injective
  apply hphi
  rw [map_mul phi]
  let evaluate :
      ((affineVariety K ((G.borelAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj)).toOver ⟶
        (borelVariety G).toOver) →
      Γ((affineVariety K ((G.borelAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj)).scheme, ⊤) :=
    fun f => f.left.appTop (borelCharacterSection G chi)
  have hm := congrArg evaluate (tensor_mul G)
  have hf := congrArg evaluate
    (affineTensorIso_fst K (G.borelAlgebra.obj : Type u) G.borelAlgebra.obj)
  have hs := congrArg evaluate
    (affineTensorIso_snd K (G.borelAlgebra.obj : Type u) G.borelAlgebra.obj)
  have ht : evaluate (affineMorphism (Bialgebra.comulAlgHom K
        (G.borelAlgebra.obj : Type u))) =
      evaluate (affineMorphism (Algebra.TensorProduct.includeLeft :
        G.borelAlgebra.obj →ₐ[K] G.borelAlgebra.obj ⊗[K] G.borelAlgebra.obj)) *
      evaluate (affineMorphism (Algebra.TensorProduct.includeRight :
        G.borelAlgebra.obj →ₐ[K] G.borelAlgebra.obj ⊗[K] G.borelAlgebra.obj)) := by
    change (Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom K
        (G.borelAlgebra.obj : Type u)).toRingHom)).appTop
          ((Scheme.ΓSpecIso (.of (G.borelAlgebra.obj : Type u))).inv _) =
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
        G.borelAlgebra.obj →ₐ[K] G.borelAlgebra.obj ⊗[K] G.borelAlgebra.obj).toRingHom)).appTop
          ((Scheme.ΓSpecIso (.of (G.borelAlgebra.obj : Type u))).inv _) *
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          G.borelAlgebra.obj →ₐ[K] G.borelAlgebra.obj ⊗[K] G.borelAlgebra.obj).toRingHom)).appTop
          ((Scheme.ΓSpecIso (.of (G.borelAlgebra.obj : Type u))).inv _)
    rw [spec_app, spec_app, spec_app]
    have hc : IsGroupLikeElem K (borelCharacterMap G chi
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) :=
      (MonoidAlgebra.isGroupLikeElem_single_one (R := K) (A := K)
        (Multiplicative.ofAdd 1)).map (borelCharacterMap G chi)
    exact (congrArg
      (Scheme.ΓSpecIso (.of ((G.borelAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj))).inv
      (groupLike_tensor (K := K)
        (borelCharacterMap G chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) hc)).trans
      (map_mul
        (Scheme.ΓSpecIso (.of ((G.borelAlgebra.obj : Type u) ⊗[K] G.borelAlgebra.obj))).inv.hom _ _)
  exact hm.trans (ht.trans (congrArg₂ (· * ·) hf.symm hs.symm))

/-- The full regular character pulls back multiplicatively along any two Borel morphisms. -/
theorem borelCharacterSection_mul (chi : G.characters)
    (X : Over (Spec (.of K))) (f g : X ⟶ (borelVariety G).toOver) :
    (f * g).left.appTop (borelCharacterSection G chi) =
      f.left.appTop (borelCharacterSection G chi) *
        g.left.appTop (borelCharacterSection G chi) := by
  exact pull_multiplicative (borelVariety G).toOver (borelCharacterSection G chi)
    (character_mul_universal G chi) X f g

/-- Pullback along the identity-valued Borel morphism is the constant function one. -/
theorem borelCharacterSection_one (chi : G.characters)
    (X : Over (Spec (.of K))) :
    (1 : X ⟶ (borelVariety G).toOver).left.appTop (borelCharacterSection G chi) = 1 := by
  have hu : η[(borelVariety G).toOver].left.appTop (borelCharacterSection G chi) = 1 := by
    change (Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom K
      (G.borelAlgebra.obj : Type u)).toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (G.borelAlgebra.obj : Type u))).inv _) = 1
    rw [spec_app]
    have hc : IsGroupLikeElem K (borelCharacterMap G chi
        (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) :=
      (MonoidAlgebra.isGroupLikeElem_single_one (R := K) (A := K)
        (Multiplicative.ofAdd 1)).map (borelCharacterMap G chi)
    have hunit : (Bialgebra.counitAlgHom K (G.borelAlgebra.obj : Type u))
        (borelCharacterMap G chi (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1)) = 1 :=
      hc.counit_eq_one
    exact (congrArg (Scheme.ΓSpecIso (.of K)).inv hunit).trans
      (map_one (Scheme.ΓSpecIso (.of K)).inv.hom)
  change (toUnit X).left.appTop
    (η[(borelVariety G).toOver].left.appTop (borelCharacterSection G chi)) = 1
  rw [hu, map_one]

end SchubertGeometry.CharacterLine
