import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

section
variable {R ι: Type*} {M N : ι → Type*} [CommRing R] [∀i, AddCommGroup (M i)][∀i, AddCommGroup (N i)]
variable [∀i, Module R (M i)][∀i, Module R (N i)]
#check DirectSum

--open TensorProduct

open DirectSum
--(∏ x i,∏ y i) -> ∏ i , (x i, y i)

--def universalprop : ∀i, M i → R := by apply?

def proddirectsum : ((∀i, N i) × (∀i, M i)) ≃ₗ[R] (∀i, ((N i) × (M i))) where
  toFun nm := fun i ↦ (nm.1 i, nm.2 i)
  map_add' x y := rfl
  map_smul' r x := rfl
  invFun nm := (fun i ↦ (nm i).1, fun i ↦ (nm i).2)
  left_inv x := rfl
  right_inv x := rfl
end
--#check TensorProduct.directSumLeft
section
variable {ι' : Type*}
variable {R ι: Type*} {M N : ι → ι' → Type*} [CommRing R] [∀i i', AddCommGroup (M i i')]
[∀i i', AddCommGroup (N i i')]
variable [∀i i', Module R (M i i')][∀i i', Module R (N i i')] [Fintype ι'][DecidableEq ι']
open DirectSum

def proddirectsum' : (⨁ (i' : ι'), (∀ i, N i i')) ≃ₗ[R] (∀ i, (⨁ i', N i i')) where
  toFun nm i := ∑i', DirectSum.of (fun i' ↦ N i i') i' (nm i' i)
  map_add' x y := by
    ext
    simp only [add_apply, Pi.add_apply, map_add]
    rw [← Finset.sum_add_distrib]
  map_smul' r nm := by
    ext i
    simp only [RingHom.id_apply, Pi.smul_apply]
    rw [Finset.smul_sum, Finset.sum_congr rfl]
    intro i' _
    rw [← DirectSum.of_smul]
    rfl
  invFun nm :=  ∑i', DirectSum.of (fun j ↦ ∀ i, N i j) i' (fun i ↦ nm i i')
  left_inv nm := by
    simp only
    convert sum_univ_of (x := nm) with j _ i
    conv_rhs => rw [← DirectSum.sum_univ_of nm]
    rw [DFinsupp.finset_sum_apply, DFinsupp.finset_sum_apply, Finset.sum_apply]
    congr with k
    by_cases h : k = j
    · subst h; simp
    · simp [of_eq_of_ne _ _ _ h]
  right_inv nm := by
    simp only
    ext i
    convert sum_univ_of (x:= nm i) with j _ i
    conv_rhs => rw [← DirectSum.sum_univ_of (nm i)]
    rw [DFinsupp.finset_sum_apply, DFinsupp.finset_sum_apply, Finset.sum_apply]
    congr with k
    by_cases h : k = j
    · subst h; simp
    · simp [of_eq_of_ne _ _ _ h]


end

section
-- trying to reconstruct toModule to work for double index

variable {R ι ι': Type*} {M : ι → ι' → Type*} [CommRing R] [∀i i', AddCommGroup (M i i')]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable [∀i i', Module R (M i i')] [Fintype ι'][DecidableEq ι']
open DirectSum
variable (φ : ∀ i', (∀i, M i i') →ₗ[R] N)
variable (R ι N)

--
def toModule'  : (⨁ (i' : ι'), (∀i, M i i'))  →ₗ[R] N := (DFinsupp.lsum ℕ) (φ )
end

section

--original toModule so I can see the code
variable {R ι: Type*} {M : ι → Type*} [CommRing R] [∀i, AddCommGroup (M i)]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable [∀i , Module R (M i)] [Fintype ι][DecidableEq ι]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable (φ : ∀ i, M i →ₗ[R] N)
variable (R ι N)
open DirectSum
/-- The linear map constructed using the universal property of the coproduct. -/
def toModule : (⨁ i, M i) →ₗ[R] N := (DFinsupp.lsum ℕ) φ


end


section

open DirectSum
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

#check DirectSum.linearEquivFunOnFintype R
#check Module.Free.ChooseBasisIndex.fintype

noncomputable def finite_free_module_iso_direct_sum
[Module.Free R M] [hM_fin : Module.Finite R M] :
M ≃ₗ[R] (⨁ i : Module.Free.ChooseBasisIndex R M, R) := by
  have h₁: M ≃ₗ[R] ((Module.Free.ChooseBasisIndex R M → R)) := Basis.equivFun (Module.Free.chooseBasis R M)
  have h₂: (⨁ i : Module.Free.ChooseBasisIndex R M, R) ≃ₗ[R] ((Module.Free.ChooseBasisIndex R M → R)) := by
    exact linearEquivFunOnFintype R (Module.Free.ChooseBasisIndex R M) fun i ↦ R
  exact LinearEquiv.trans h₁ h₂.symm

open scoped TensorProduct
variable {ι : Type*}
variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]


-- noncomputable def tensorProdbilinear' [Module.Free R M] [Module.Finite R M] :
--     M ⊗[R] (∀ i, N i) →ₗ[R] ∀ i, (M ⊗[R] N i) :=
--   TensorProduct.lift {
--     toFun := fun m =>
--       LinearMap.pi fun i =>
--         (TensorProduct.mk R M (N i)).comp (LinearMap.proj i)
--     map_add' := fun m₁ m₂ => by
--       ext n i
--       simp only [LinearMap.add_apply, Pi.add_apply, LinearMap.proj_apply, LinearMap.comp_apply,
--         TensorProduct.mk_apply, TensorProduct.add_tmul],
--     map_smul' := fun r m => by
--       ext n i
--       simp only [LinearMap.smul_apply, Pi.smul_apply, LinearMap.proj_apply, LinearMap.comp_apply,
--         TensorProduct.mk_apply, TensorProduct.smul_tmul, RingHom.id_apply]
--   }


noncomputable def tensorProdbilinear' [Module.Free R M] [Module.Finite R M]:
   M ⊗[R] (∀ i, N i) →ₗ[R] ∀ i, (M ⊗[R] N i) :=
  TensorProduct.lift <| {
      toFun := fun m ↦ {
        toFun := fun n i ↦ m ⊗ₜ[R] n i
        map_add' := by
          intro x y
          ext i
          simp only [add_apply, Pi.add_apply, map_add]
          exact TensorProduct.tmul_add m (x i) (y i)
        map_smul' := by
          intro m n
          ext i
          simp only [Pi.smul_apply, TensorProduct.tmul_smul, TensorProduct.zero_tmul, smul_zero,
          RingHom.id_apply]
      }
      map_add' := by
        intro m₁ m₂
        ext n i
        simp only [add_apply, Pi.add_apply, map_add]
        exact TensorProduct.add_tmul m₁ m₂ (n i)
      map_smul' := by
        intro r m
        ext n i
        simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
          Pi.smul_apply]
        rfl
        }


noncomputable def tensorProdbilinear [Module.Free R M] [Module.Finite R M]:
   M ⊗[R] (∀ i, N i) ≃ₗ[R] ∀ i, (M ⊗[R] N i)  := by
   refine LinearEquiv.ofBijective (tensorProdbilinear') ⟨?_, ?_⟩
   · apply (injective_iff_map_eq_zero' _).mpr
     intro a
     constructor
     · intro h
       have h₁ :  M ⊗[R] (∀ i, N i) ≃ₗ[R]  (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] (∀i, N i) :=
      TensorProduct.congr finite_free_module_iso_direct_sum (LinearEquiv.refl R ((i : ι) → N i))
       have h₂ : (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] (∀i, N i) ≃ₗ[R]
        ∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] N i := by
        apply?
        sorry
       have h₃ : (∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] N i )≃ₗ[R] ∀i, (M ⊗[R] N i):= by
        have (i: ι): (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] N i  ≃ₗ[R]  M ⊗[R] N i := by
          exact LinearEquiv.rTensor (N i) (finite_free_module_iso_direct_sum.symm)
        exact LinearEquiv.piCongrRight this
       obtain ⟨b, hb⟩ := LinearEquiv.surjective (h₁.symm) a
       rw [← hb]
       have : h₃ (h₂ b) = tensorProdbilinear' (h₁.symm b) := by sorry

noncomputable def tensorProdEquiv [Module.Free R M] [Module.Finite R M]:
  M ⊗[R] (∀ i, N i) ≃ₗ[R] ∀ i, (M ⊗[R] N i) := by
  have h₁ :  M ⊗[R] (∀ i, N i) ≃ₗ[R]  (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] (∀i, N i) :=
    TensorProduct.congr finite_free_module_iso_direct_sum (LinearEquiv.refl R ((i : ι) → N i))
  have h₂: (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] (∀i, N i) ≃ₗ[R]
    ⨁ i' : (Module.Free.ChooseBasisIndex R M), R ⊗[R] (∀i, N i) := by
    apply TensorProduct.directSumLeft
  have h₃: (⨁ i' : (Module.Free.ChooseBasisIndex R M), (∀i, N i)) ≃ₗ[R]
    ⨁ i' : (Module.Free.ChooseBasisIndex R M), R ⊗[R] (∀i, N i) := by
   have := fun (i': (Module.Free.ChooseBasisIndex R M)) ↦ TensorProduct.lid R ((i : ι) → N i)
   have h₁:= LinearEquiv.piCongrRight (this)
   have h₂:= linearEquivFunOnFintype R (Module.Free.ChooseBasisIndex R M) (fun i' ↦ (R ⊗[R] ∀i, N i))
   have h₃:= linearEquivFunOnFintype R (Module.Free.ChooseBasisIndex R M) (fun i' ↦ (∀i, N i))
   have h₄:= LinearEquiv.trans h₂ h₁
   exact (LinearEquiv.trans h₄ h₃.symm).symm
  let a:= ∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, N i)
  have h₄: (⨁ (i' : Module.Free.ChooseBasisIndex R M), (i : ι) → N i) ≃ₗ[R] ∀i, ⨁ i' : Module.Free.ChooseBasisIndex R M, N i := by
    exact proddirectsum' --(ι':= Module.Free.ChooseBasisIndex R M)--why does this work even though N isn't double indexed?
  have h₅: (∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, N i)) ≃ₗ[R] ∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, R ⊗[R] N i) := by
    have (i: ι):= fun (i': (Module.Free.ChooseBasisIndex R M)) ↦ TensorProduct.lid R (N i)
    have h₁ (i: ι):= LinearEquiv.piCongrRight (this i)
    have h₂ (i: ι):= linearEquivFunOnFintype R (Module.Free.ChooseBasisIndex R M) (fun i' ↦ (R ⊗[R] N i))
    have h₃ (i :ι):= linearEquivFunOnFintype R (Module.Free.ChooseBasisIndex R M) (fun i' ↦ ( N i))
    have h₄ (i: ι):= LinearEquiv.trans (h₂ i) (h₁ i)
    have h₅ (i: ι):= (LinearEquiv.trans (h₄ i) (h₃ i).symm).symm
    exact LinearEquiv.piCongrRight h₅
  have h₆ : (∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, R ⊗[R] N i)) ≃ₗ[R] ∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] N i := by
    have (i: ι): (⨁ i' : Module.Free.ChooseBasisIndex R M, R ⊗[R] N i) ≃ₗ[R] (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] N i := by
      exact (TensorProduct.directSumLeft R (fun i₁ ↦ R) (N i)).symm
    exact LinearEquiv.piCongrRight this
  have h₇ : (∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] N i) ≃ₗ[R] ∀i, (M ⊗[R] N i) := by
    have (i: ι): (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] N i  ≃ₗ[R]  M ⊗[R] N i := by
      exact LinearEquiv.rTensor (N i) (finite_free_module_iso_direct_sum.symm)
    exact LinearEquiv.piCongrRight this
  have g₁:= LinearEquiv.trans h₁ h₂
  have g₂ := LinearEquiv.trans g₁ h₃.symm
  have g₃ := LinearEquiv.trans g₂ h₄
  have g₄ := LinearEquiv.trans g₃ h₅
  have g₅ := LinearEquiv.trans g₄ h₆
  exact LinearEquiv.trans g₅ h₇

noncomputable def tensorProdEquiv_apply [Module.Free R M] [Module.Finite R M]
  (m : M) (n: ∀i, N i) : tensorProdbilinear' (m ⊗ₜ[R] n) = fun i ↦ m ⊗ₜ[R] n i := by
    unfold tensorProdbilinear'
    simp only [LinearEquiv.coe_mk, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]


end
