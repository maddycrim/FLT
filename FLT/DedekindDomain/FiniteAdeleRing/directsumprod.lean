import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

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

open DirectSum
variable {R ι : Type*}
variable [Semiring R] {φ ψ χ : ι → Type*}
variable [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]
variable [(i : ι) → AddCommMonoid (ψ i)] [(i : ι) → Module R (ψ i)]
/-- Proof that if we have a family of isomorphisms then the direct sums are isomorphic
given a fintype ι. Can be proved for infinite type?
-/
noncomputable def sumCongrRight [Fintype ι] [DecidableEq ι] (e : (i : ι) → φ i ≃ₗ[R] ψ i) : (⨁i, φ i) ≃ₗ[R] ⨁i,ψ i where
  toFun f :=  ∑i, DirectSum.of ψ i ((e i) (f i))
  invFun f := ∑i, DirectSum.of φ i ((e i).symm (f i))
  map_add' f g := by
    simp only [add_apply, map_add]
    rw [← Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [RingHom.id_apply]
    rw [Finset.smul_sum, Finset.sum_congr rfl]
    intro i' _
    rw [← DirectSum.of_smul, ← map_smul]
    rfl
  left_inv f := by
    simp only
    convert sum_univ_of (x := f) with j hj i
    have : (e j).symm ((∑ x : ι, (of ψ x) ((e x) (f x))) j) = f j ↔ (e j ) ((e j).symm ((∑ x : ι, (of ψ x) ((e x) (f x))) j)) = (e j) (f j) := by
      exact Iff.symm (EmbeddingLike.apply_eq_iff_eq (e j))
    apply this.mpr
    have : (e j) ((e j).symm ((∑ x : ι, (of ψ x) ((e x) (f x))) j)) =  (((∑ x : ι, (of ψ x) ((e x) (f x))) j)) := by
      exact LinearEquiv.apply_symm_apply (e j) ((∑ x : ι, (of ψ x) ((e x) (f x))) j)
    rw [this]
    rw [DFinsupp.finset_sum_apply]
    rw [Finset.sum_eq_single j]
    exact of_eq_same j ((e j) (f j))
    exact fun b a a ↦ of_eq_of_ne b j ((e b) (f b)) a
    exact fun a ↦ False.elim (a hj)
  right_inv f := by
    simp only
    convert sum_univ_of (x := f) with j hj i
    have : (e j) ((∑ x : ι, (of φ x) ((e x).symm (f x))) j) = f j ↔ (e j ).symm ((e j) ((∑ x : ι, (of φ x) ((e x).symm (f x))) j)) = (e j).symm (f j) := by
      exact Iff.symm (EmbeddingLike.apply_eq_iff_eq (e j).symm)
    apply this.mpr
    have : (e j).symm ((e j) ((∑ x : ι, (of φ x) ((e x).symm (f x))) j)) =  (((∑ x : ι, (of φ x) ((e x).symm (f x))) j)) := by
      exact LinearEquiv.apply_symm_apply (e j).symm ((∑ x : ι, (of φ x) ((e x).symm (f x))) j)
    rw [this]
    rw [DFinsupp.finset_sum_apply]
    rw [Finset.sum_eq_single j]
    exact of_eq_same j ((e j).symm (f j))
    exact fun b a a ↦ of_eq_of_ne b j ((e b).symm (f b)) a
    exact fun a ↦ False.elim (a hj)


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

-- initial proof of isomorphism, this requires proving a series of isomorphisms which is difficult to
--break down in the proof I need
-- noncomputable def tensorProdEquiv [Module.Free R M] [Module.Finite R M]:
--   M ⊗[R] (∀ i, N i) ≃ₗ[R] ∀ i, (M ⊗[R] N i) := by
--   have h₁ :  M ⊗[R] (∀ i, N i) ≃ₗ[R]  (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] (∀i, N i) :=
--     TensorProduct.congr finite_free_module_iso_direct_sum (LinearEquiv.refl R ((i : ι) → N i))
--   have h₂: (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] (∀i, N i) ≃ₗ[R]
--     ⨁ i' : (Module.Free.ChooseBasisIndex R M), R ⊗[R] (∀i, N i) := by
--     apply TensorProduct.directSumLeft
--   have h₃: (⨁ i' : (Module.Free.ChooseBasisIndex R M), (∀i, N i)) ≃ₗ[R]
--     ⨁ i' : (Module.Free.ChooseBasisIndex R M), R ⊗[R] (∀i, N i) := by
--    have := fun (i': (Module.Free.ChooseBasisIndex R M)) ↦ TensorProduct.lid R ((i : ι) → N i)
--    have h₁:= LinearEquiv.piCongrRight (this)
--    have h₂:= linearEquivFunOnFintype R (Module.Free.ChooseBasisIndex R M) (fun i' ↦ (R ⊗[R] ∀i, N i))
--    have h₃:= linearEquivFunOnFintype R (Module.Free.ChooseBasisIndex R M) (fun i' ↦ (∀i, N i))
--    have h₄:= LinearEquiv.trans h₂ h₁
--    exact (LinearEquiv.trans h₄ h₃.symm).symm
--   let a:= ∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, N i)
--   have h₄: (⨁ (i' : Module.Free.ChooseBasisIndex R M), (i : ι) → N i) ≃ₗ[R] ∀i, ⨁ i' : Module.Free.ChooseBasisIndex R M, N i := by
--     exact proddirectsum' --(ι':= Module.Free.ChooseBasisIndex R M)--why does this work even though N isn't double indexed?
--   have h₅: (∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, N i)) ≃ₗ[R] ∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, R ⊗[R] N i) := by
--     have (i: ι):= fun (i': (Module.Free.ChooseBasisIndex R M)) ↦ TensorProduct.lid R (N i)
--     have h₁ (i: ι):= LinearEquiv.piCongrRight (this i)
--     have h₂ (i: ι):= linearEquivFunOnFintype R (Module.Free.ChooseBasisIndex R M) (fun i' ↦ (R ⊗[R] N i))
--     have h₃ (i :ι):= linearEquivFunOnFintype R (Module.Free.ChooseBasisIndex R M) (fun i' ↦ ( N i))
--     have h₄ (i: ι):= LinearEquiv.trans (h₂ i) (h₁ i)
--     have h₅ (i: ι):= (LinearEquiv.trans (h₄ i) (h₃ i).symm).symm
--     exact LinearEquiv.piCongrRight h₅
--   have h₆ : (∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, R ⊗[R] N i)) ≃ₗ[R] ∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] N i := by
--     have (i: ι): (⨁ i' : Module.Free.ChooseBasisIndex R M, R ⊗[R] N i) ≃ₗ[R] (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] N i := by
--       exact (TensorProduct.directSumLeft R (fun i₁ ↦ R) (N i)).symm
--     exact LinearEquiv.piCongrRight this
--   have h₇ : (∀i, (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] N i) ≃ₗ[R] ∀i, (M ⊗[R] N i) := by
--     have (i: ι): (⨁ i' : Module.Free.ChooseBasisIndex R M, R) ⊗[R] N i  ≃ₗ[R]  M ⊗[R] N i := by
--       exact LinearEquiv.rTensor (N i) (finite_free_module_iso_direct_sum.symm)
--     exact LinearEquiv.piCongrRight this
--   have g₁:= LinearEquiv.trans h₁ h₂
--   have g₂ := LinearEquiv.trans g₁ h₃.symm
--   have g₃ := LinearEquiv.trans g₂ h₄
--   have g₄ := LinearEquiv.trans g₃ h₅
--   have g₅ := LinearEquiv.trans g₄ h₆
--   exact LinearEquiv.trans g₅ h₇



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



variable (R M N)
noncomputable def h₁ [Module.Free R M] [Module.Finite R M]:  M ⊗[R] (∀ i, N i) ≃ₗ[R]  ( Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] (∀i, N i) :=
      TensorProduct.congr (Module.Free.repr R M) (LinearEquiv.refl R ((i : ι) → N i))


#check finsuppTensorFinsupp
#check linearEquivFunOnFintype
open TensorProduct
noncomputable def h₂ [Module.Free R M] [Module.Finite R M] : ( Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] (∀i, N i)
  ≃ₗ[R] ∀i, ( Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] (N i) :=
  finsuppScalarLeft R (∀i, N i) (Module.Free.ChooseBasisIndex R M) ≪≫ₗ
    (finsuppLEquivDirectSum R (∀i, N i) (Module.Free.ChooseBasisIndex R M)) ≪≫ₗ
    proddirectsum'  ≪≫ₗ
    LinearEquiv.piCongrRight (fun i ↦(finsuppLEquivDirectSum R (N i) (Module.Free.ChooseBasisIndex R M)).symm)
    ≪≫ₗ  LinearEquiv.piCongrRight (fun i ↦
     (finsuppScalarLeft R (N i) (Module.Free.ChooseBasisIndex R M)).symm)

noncomputable def h₃ [Module.Free R M] [Module.Finite R M] : (∀i, ( Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] N i )≃ₗ[R] ∀i, (M ⊗[R] N i):= by
  exact LinearEquiv.piCongrRight (fun i ↦ (LinearEquiv.rTensor (N i) (Module.Free.repr R M).symm) )

variable [DecidableEq ι]


noncomputable def tensorProdbilinear [Module.Free R M] [Module.Finite R M]:
   M ⊗[R] (∀ i, N i) ≃ₗ[R] ∀ i, (M ⊗[R] N i)  := by
   refine LinearEquiv.ofBijective (TensorProduct.lift <| {
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
    ) ⟨?_, ?_⟩
   · apply (injective_iff_map_eq_zero' _).mpr
     intro a
     constructor
     · intro h
       obtain ⟨b, hb⟩ := LinearEquiv.surjective ((h₁ R M N).symm) a
       rw [← hb]
       have : LinearMap.lcomp R _ (h₁ R M N).symm (tensorProdbilinear' (R:=R) (M:=M) (N:=N))
        (M:= (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] ((i : ι) → N i)) =
        LinearMap.lcomp R ((i : ι) → M ⊗[R] N i) (h₂ R M N) (h₃ R M N)
        (M:= (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] ((i : ι) → N i))
        (Nₗ := (i : ι) → ( Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] N i) := by
        apply TensorProduct.AlgebraTensorModule.ext
        intro x y
        simp only [LinearMap.lcomp_apply, LinearEquiv.coe_coe]
        have : ((h₂ R M N) (x ⊗ₜ[R] y)) = (fun i ↦ (x ⊗ₜ[R] y i)) := by
          unfold h₂
          simp only [LinearEquiv.trans_apply]
          rw [finsuppScalarLeft_apply_tmul, Finsupp.sum, map_sum]
          simp only [finsuppLEquivDirectSum_single]
          unfold proddirectsum'
          simp only [LinearEquiv.coe_mk]
          sorry

        -- unfold h₂ h₃ tensorProdbilinear' h₁
        -- simp only [congr_symm_tmul, LinearEquiv.refl_symm, LinearEquiv.refl_apply, lift.tmul,
        --   LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.trans_apply]
        -- refine funext ?_
        -- intro i
        -- simp only [LinearEquiv.piCongrRight_apply]
        -- rw [finsuppScalarLeft_apply_tmul, Finsupp.sum, map_sum]
        -- simp only [finsuppLEquivDirectSum_single]
        -- unfold proddirectsum'
        -- simp only [LinearEquiv.coe_mk]
        -- have : (∑ x_1 : Module.Free.ChooseBasisIndex R M,
        --   (of (fun i' ↦ N i) x_1)
        --     ((∑ x_2 ∈ x.support, (lof R (Module.Free.ChooseBasisIndex R M)
        --      (fun i ↦ (i : ι) → N i) x_2) (x x_2 • y)) x_1
        --       i)) = ∑ x_1 : Module.Free.ChooseBasisIndex R M,
        --   (of (fun i' ↦ N i) x_1) (x x_1 • y i) := by
        --   apply Finset.sum_congr
        --   rfl
        --   intro i' hi'
        --   apply (Function.Injective.eq_iff (DirectSum.of_injective i')).mpr
        --   rw [DFinsupp.finset_sum_apply, Finset.sum_eq_single i']
        --   rw [lof_apply R i' (x i' • y) (M := fun (j:Module.Free.ChooseBasisIndex R M) ↦ (∀i, N i))]
        --   rfl
        --   intro j hj hj'
        --   rw [lof_eq_of]
        --   exact of_eq_of_ne j i' (x j • y) hj' (β := (fun i ↦ (i : ι) → N i) )
        --   intro hi''
        --   rw [Finsupp.not_mem_support_iff.mp, zero_smul]
        --   exact lof_apply R i' 0
        --   exact hi''
        -- rw [this]
        -- simp?
        -- unfold finsuppLEquivDirectSum
        -- simp only [ne_eq]
        -- haveI (i : ι) : DecidableEq (N i) := Classical.decEq (N i)

        sorry
       sorry
     sorry
   · sorry





noncomputable def tensorProdEquiv_apply [Module.Free R M] [Module.Finite R M]
  (m : M) (n: ∀i, N i) : (tensorProdbilinear R M N) (m ⊗ₜ[R] n) = ( fun i ↦ m ⊗ₜ[R] n i ):= by
    exact rfl
