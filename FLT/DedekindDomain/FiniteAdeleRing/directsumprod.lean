import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic



section
variable {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {R ι : Type*} [CommRing R]
  {M N : ι → ι' → Type*} [∀ i i', AddCommGroup (M i i')] [∀ i i', AddCommGroup (N i i')]
  [∀i i', Module R (M i i')] [∀i i', Module R (N i i')]
open DirectSum

def directSumProd_equiv_prodSum : (⨁ (i' : ι'), (∀ i, N i i')) ≃ₗ[R] (∀ i, (⨁ i', N i i')) where
  toFun nm i := ∑ i', DirectSum.of (fun i' ↦ N i i') i' (nm i' i)
  map_add' x y := by
    simp only [add_apply, Pi.add_apply, map_add]
    ext i
    rw [Finset.sum_add_distrib]
    rfl
  map_smul' r nm := by
    ext i
    simp only [RingHom.id_apply, Pi.smul_apply]
    rw [Finset.smul_sum, Finset.sum_congr rfl]
    intro i' _
    rw [← DirectSum.of_smul]
    rfl
  invFun nm :=  ∑ i', DirectSum.of (fun j ↦ ∀ i, N i j) i' (fun i ↦ nm i i')
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
    refine funext (fun i ↦ ?_)
    convert sum_univ_of (x := nm i) with j _ i
    conv_rhs => rw [← DirectSum.sum_univ_of (nm i)]
    rw [DFinsupp.finset_sum_apply, DFinsupp.finset_sum_apply, Finset.sum_apply]
    congr with k
    by_cases h : k = j
    · subst h; simp
    · simp [of_eq_of_ne _ _ _ h]

end

-- open DirectSum
-- variable {R ι : Type*}
-- variable [Semiring R] {φ ψ χ : ι → Type*}
-- variable [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]
-- variable [(i : ι) → AddCommMonoid (ψ i)] [(i : ι) → Module R (ψ i)]
-- /-- Proof that if we have a family of isomorphisms then the direct sums are isomorphic
-- given a fintype ι. Can be proved for infinite type?
-- -/
-- noncomputable def sumCongrRight [Fintype ι] [DecidableEq ι] (e : (i : ι) → φ i ≃ₗ[R] ψ i) : (⨁i, φ i) ≃ₗ[R] ⨁i,ψ i where
--   toFun f :=  ∑i, DirectSum.of ψ i ((e i) (f i))
--   invFun f := ∑i, DirectSum.of φ i ((e i).symm (f i))
--   map_add' f g := by
--     simp only [add_apply, map_add]
--     rw [← Finset.sum_add_distrib]
--   map_smul' r f := by
--     simp only [RingHom.id_apply]
--     rw [Finset.smul_sum, Finset.sum_congr rfl]
--     intro i' _
--     rw [← DirectSum.of_smul, ← map_smul]
--     rfl
--   left_inv f := by
--     simp only
--     convert sum_univ_of (x := f) with j hj i
--     have : (e j).symm ((∑ x : ι, (of ψ x) ((e x) (f x))) j) = f j ↔ (e j ) ((e j).symm ((∑ x : ι, (of ψ x) ((e x) (f x))) j)) = (e j) (f j) := by
--       exact Iff.symm (EmbeddingLike.apply_eq_iff_eq (e j))
--     apply this.mpr
--     have : (e j) ((e j).symm ((∑ x : ι, (of ψ x) ((e x) (f x))) j)) =  (((∑ x : ι, (of ψ x) ((e x) (f x))) j)) := by
--       exact LinearEquiv.apply_symm_apply (e j) ((∑ x : ι, (of ψ x) ((e x) (f x))) j)
--     rw [this]
--     rw [DFinsupp.finset_sum_apply]
--     rw [Finset.sum_eq_single j]
--     exact of_eq_same j ((e j) (f j))
--     exact fun b a a ↦ of_eq_of_ne b j ((e b) (f b)) a
--     exact fun a ↦ False.elim (a hj)
--   right_inv f := by
--     simp only
--     convert sum_univ_of (x := f) with j hj i
--     have : (e j) ((∑ x : ι, (of φ x) ((e x).symm (f x))) j) = f j ↔ (e j ).symm ((e j) ((∑ x : ι, (of φ x) ((e x).symm (f x))) j)) = (e j).symm (f j) := by
--       exact Iff.symm (EmbeddingLike.apply_eq_iff_eq (e j).symm)
--     apply this.mpr
--     have : (e j).symm ((e j) ((∑ x : ι, (of φ x) ((e x).symm (f x))) j)) =  (((∑ x : ι, (of φ x) ((e x).symm (f x))) j)) := by
--       exact LinearEquiv.apply_symm_apply (e j).symm ((∑ x : ι, (of φ x) ((e x).symm (f x))) j)
--     rw [this]
--     rw [DFinsupp.finset_sum_apply]
--     rw [Finset.sum_eq_single j]
--     exact of_eq_same j ((e j).symm (f j))
--     exact fun b a a ↦ of_eq_of_ne b j ((e b).symm (f b)) a
--     exact fun a ↦ False.elim (a hj)


-- #check DirectSum.linearEquivFunOnFintype R
-- #check Module.Free.ChooseBasisIndex.fintype

-- noncomputable def finite_free_module_iso_direct_sum
-- [Module.Free R M] [hM_fin : Module.Finite R M] :
-- M ≃ₗ[R] (⨁ i : Module.Free.ChooseBasisIndex R M, R) := by
--   have h₁: M ≃ₗ[R] ((Module.Free.ChooseBasisIndex R M → R)) := Basis.equivFun (Module.Free.chooseBasis R M)
--   have h₂: (⨁ i : Module.Free.ChooseBasisIndex R M, R) ≃ₗ[R] ((Module.Free.ChooseBasisIndex R M → R)) := by
--     exact linearEquivFunOnFintype R (Module.Free.ChooseBasisIndex R M) fun i ↦ R
--   exact LinearEquiv.trans h₁ h₂.symm

-- open scoped TensorProduct


-- noncomputable def tensorProdbilinear' [Module.Free R M] [Module.Finite R M]:
--    M ⊗[R] (∀ i, N i) →ₗ[R] ∀ i, (M ⊗[R] N i) :=
--   TensorProduct.lift <| {
--       toFun := fun m ↦ {
--         toFun := fun n i ↦ m ⊗ₜ[R] n i
--         map_add' := by
--           intro x y
--           ext i
--           simp only [add_apply, Pi.add_apply, map_add]
--           exact TensorProduct.tmul_add m (x i) (y i)
--         map_smul' := by
--           intro m n
--           ext i
--           simp only [Pi.smul_apply, TensorProduct.tmul_smul, TensorProduct.zero_tmul, smul_zero,
--           RingHom.id_apply]
--       }
--       map_add' := by
--         intro m₁ m₂
--         ext n i
--         simp only [add_apply, Pi.add_apply, map_add]
--         exact TensorProduct.add_tmul m₁ m₂ (n i)
--       map_smul' := by
--         intro r m
--         ext n i
--         simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
--           Pi.smul_apply]
--         rfl
--         }


section

open DirectSum
variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]


-- NEEDED
open TensorProduct
noncomputable def moduleTensorProdEquiv :
    M ⊗[R] (∀ i, N i) ≃ₗ[R] (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] (∀ i, N i) :=
  TensorProduct.congr (Module.Free.repr R M) (LinearEquiv.refl R ((i : ι) → N i))

noncomputable def TensorProdEquivProdTensor :
    (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] (∀ i, N i) ≃ₗ[R]
      ∀ i, ( Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] (N i) :=
  finsuppScalarLeft R (∀i, N i) (Module.Free.ChooseBasisIndex R M) ≪≫ₗ
    (finsuppLEquivDirectSum R (∀i, N i) (Module.Free.ChooseBasisIndex R M)) ≪≫ₗ
    directSumProd_equiv_prodSum  ≪≫ₗ
    LinearEquiv.piCongrRight (fun i ↦(finsuppLEquivDirectSum R (N i)
    (Module.Free.ChooseBasisIndex R M)).symm)
    ≪≫ₗ  LinearEquiv.piCongrRight (fun i ↦
     (finsuppScalarLeft R (N i) (Module.Free.ChooseBasisIndex R M)).symm)

noncomputable def prodTensorEquiv :
    (∀ i, (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] N i) ≃ₗ[R] ∀ i, (M ⊗[R] N i):=
  LinearEquiv.piCongrRight (fun i ↦ (LinearEquiv.rTensor (N i) (Module.Free.repr R M).symm))

noncomputable def tensorProdbilinear_map :
    M ⊗[R] (∀ i, N i) ≃ₗ[R] ∀ i, (M ⊗[R] N i) :=
  (moduleTensorProdEquiv R M N) ≪≫ₗ (TensorProdEquivProdTensor R M N) ≪≫ₗ (prodTensorEquiv R M N)

lemma tensorProdbilinear_map_apply (m : M) (n : ∀ i, N i) :
    tensorProdbilinear_map R M N (m ⊗ₜ n) = fun i ↦ (m ⊗ₜ n i) := by
  unfold tensorProdbilinear_map
  simp [moduleTensorProdEquiv]
  -- the goal now mentions `(Module.Free.repr R M) m` which has type `(some set) →₀ R`
  -- i.e. `Finsupp`, so we can (rather inelegantly) change the goal so that it
  -- doesn't mention m at all and only mentions `m'`, this finitely-supported function.
  let m' := (Module.Free.repr R M) m
  have hm' : (Module.Free.repr R M).symm m' = m := by simp [m']
  rw [← hm']
  simp
  -- Now the goal only has m' not m so we can apply an induction principle
  induction m' using Finsupp.induction_linear
  · -- goal true for zero function
    ext
    simp
  · -- goal preserved under addition
    ext i
    simp_all [add_tmul]
  · -- what's left: goal is true for functions supported at one place
    rename_i j r
    -- STP for m' the function sending j to r and everything else to 0
    -- randomly move an equiv to the other side out of hope more
    -- than anything else
    rw [← LinearEquiv.eq_symm_apply]
    simp [prodTensorEquiv]
    ext i
    simp only [LinearEquiv.piCongrRight_apply, LinearEquiv.rTensor_symm_tmul, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply, m']
    -- we are surely close!
    -- ⊢ (TensorProdEquivProdTensor R M N) (Finsupp.single j r ⊗ₜ[R] n) i = Finsupp.single j r ⊗ₜ[R] n i
    -- Kevin got here
    rw [TensorProdEquivProdTensor]
    simp only [LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
    rw [LinearEquiv.symm_apply_eq]
    ext k
    rw [finsuppScalarLeft_apply, LinearMap.rTensor_tmul, Finsupp.lapply_apply,
      TensorProduct.lid_tmul, Finsupp.single_apply, ite_smul, zero_smul, ← Finsupp.single_apply]
    apply congrFun
    apply congrArg
    clear k hm' m' m
    rw [LinearEquiv.symm_apply_eq,finsuppLEquivDirectSum_single,
      finsuppScalarLeft_apply_tmul, Finsupp.sum_single_index (by simp),
      finsuppLEquivDirectSum_single, DirectSum.lof_eq_of, DirectSum.lof_eq_of, directSumProd_equiv_prodSum]
    simp_rw [← LinearEquiv.toFun_eq_coe]
    conv_lhs =>
      enter [2, x]
      rw [DirectSum.of_apply]
      simp only [Eq.recOn.eq_def, eq_rec_constant, dif_eq_if]
      rw [ite_apply, Pi.zero_apply, Pi.smul_apply, apply_ite (DFunLike.coe _), AddMonoidHom.map_zero]
    apply Fintype.sum_dite_eq


#exit

#check LinearMap.single
#check LinearMap.proj

noncomputable def tensorProdbilinear_map_apply' [Module.Free R M] [Module.Finite R M]
    (m : M) (n : ∀ i, N i) (i : ι) :
    tensorProdbilinear_map (R := R) M N (m ⊗ₜ n) i = (m ⊗ₜ n i) := by
  rw [tensorProdbilinear_map_apply]


variable {M' : Type*}[AddCommGroup M'] [Module R M'] [DecidableEq ι]
noncomputable def comm' : M ⊗[R] M' ≃ₗ[R] M' ⊗[R] M :=
  LinearEquiv.ofLinear (lift (mk R M' M).flip) (lift (mk R M M').flip) (ext' fun _ _ => rfl)
     (ext' fun _ _ => rfl)
-- #check DFinsupp.finset_sum_apply
-- #check Finset.sum_eq_single
-- noncomputable def tensorProdbilinear [Module.Free R M] [Module.Finite R M]:
--    M ⊗[R] (∀ i, N i) ≃ₗ[R] ∀ i, (M ⊗[R] N i)  := by
--    refine LinearEquiv.ofBijective (TensorProduct.lift <| {
--       toFun := fun m ↦ {
--         toFun := fun n i ↦ m ⊗ₜ[R] n i
--         map_add' := by
--           intro x y
--           ext i
--           simp only [add_apply, Pi.add_apply, map_add]
--           exact TensorProduct.tmul_add m (x i) (y i)
--         map_smul' := by
--           intro m n
--           ext i
--           simp only [Pi.smul_apply, TensorProduct.tmul_smul, TensorProduct.zero_tmul, smul_zero,
--           RingHom.id_apply]
--       }
--       map_add' := by
--         intro m₁ m₂
--         ext n i
--         simp only [add_apply, Pi.add_apply, map_add]
--         exact TensorProduct.add_tmul m₁ m₂ (n i)
--       map_smul' := by
--         intro r m
--         ext n i
--         simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
--           Pi.smul_apply]
--         rfl
--         }
--     ) ⟨?_, ?_⟩
--    · apply (injective_iff_map_eq_zero' _).mpr
--      intro a
--      constructor
--      · intro h
--        obtain ⟨b, hb⟩ := LinearEquiv.surjective ((h₁ R M N).symm) a
--        rw [← hb]
--        have : LinearMap.lcomp R _ (h₁ R M N).symm (tensorProdbilinear' (R:=R) (M:=M) (N:=N))
--         (M:= (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] ((i : ι) → N i)) =
--         LinearMap.lcomp R ((i : ι) → M ⊗[R] N i) (h₂ R M N) (h₃ R M N)
--         (M:= (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] ((i : ι) → N i))
--         (Nₗ := (i : ι) → ( Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] N i) := by
--         apply TensorProduct.AlgebraTensorModule.ext
--         intro x y
--         simp only [LinearMap.lcomp_apply, LinearEquiv.coe_coe]
--         have : ((h₂ R M N) (x ⊗ₜ[R] y)) = (fun i ↦ (x ⊗ₜ[R] y i)) := by
--           unfold h₂
--           simp only [LinearEquiv.trans_apply]
--           rw [finsuppScalarLeft_apply_tmul, Finsupp.sum, map_sum]
--           simp only [finsuppLEquivDirectSum_single]
--           unfold proddirectsum'
--           simp only [LinearEquiv.coe_mk]
--           sorry

--         -- unfold h₂ h₃ tensorProdbilinear' h₁
--         -- simp only [congr_symm_tmul, LinearEquiv.refl_symm, LinearEquiv.refl_apply, lift.tmul,
--         --   LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.trans_apply]
--         -- refine funext ?_
--         -- intro i
--         -- simp only [LinearEquiv.piCongrRight_apply]
--         -- rw [finsuppScalarLeft_apply_tmul, Finsupp.sum, map_sum]
--         -- simp only [finsuppLEquivDirectSum_single]
--         -- unfold proddirectsum'
--         -- simp only [LinearEquiv.coe_mk]
--         -- have : (∑ x_1 : Module.Free.ChooseBasisIndex R M,
--         --   (of (fun i' ↦ N i) x_1)
--         --     ((∑ x_2 ∈ x.support, (lof R (Module.Free.ChooseBasisIndex R M)
--         --      (fun i ↦ (i : ι) → N i) x_2) (x x_2 • y)) x_1
--         --       i)) = ∑ x_1 : Module.Free.ChooseBasisIndex R M,
--         --   (of (fun i' ↦ N i) x_1) (x x_1 • y i) := by
--         --   apply Finset.sum_congr
--         --   rfl
--         --   intro i' hi'
--         --   apply (Function.Injective.eq_iff (DirectSum.of_injective i')).mpr
--         --   rw [DFinsupp.finset_sum_apply, Finset.sum_eq_single i']
--         --   rw [lof_apply R i' (x i' • y) (M := fun (j:Module.Free.ChooseBasisIndex R M) ↦ (∀i, N i))]
--         --   rfl
--         --   intro j hj hj'
--         --   rw [lof_eq_of]
--         --   exact of_eq_of_ne j i' (x j • y) hj' (β := (fun i ↦ (i : ι) → N i) )
--         --   intro hi''
--         --   rw [Finsupp.not_mem_support_iff.mp, zero_smul]
--         --   exact lof_apply R i' 0
--         --   exact hi''
--         -- rw [this]
--         -- simp?
--         -- unfold finsuppLEquivDirectSum
--         -- simp only [ne_eq]
--         -- haveI (i : ι) : DecidableEq (N i) := Classical.decEq (N i)

--         sorry
--        sorry
--      sorry
--    · sorry





-- noncomputable def tensorProdEquiv_apply [Module.Free R M] [Module.Finite R M]
--   (m : M) (n: ∀i, N i) : (tensorProdbilinear R M N) (m ⊗ₜ[R] n) = ( fun i ↦ m ⊗ₜ[R] n i ):= by
--     exact rfl


-- -- have (l : L) (a : ProdAdicCompletions A K) :
-- --         SemialgHom.baseChange_of_algebraMap (ProdAdicCompletions.baseChange A K L B) (l ⊗ₜ a) = 0
-- --         → (l ⊗ₜ a = (0:L ⊗[K] ProdAdicCompletions A K) ) := by
-- --           intro h
-- --           simp [SemialgHom.baseChange_of_algebraMap, SemialgHom.toLinearMap_eq_coe] at h
-- --           rw [Algebra.ofId_apply] at h
-- --           rw [← Algebra.smul_def] at h
-- --           have h₁: l = 0 ∨ (ProdAdicCompletions.baseChange A K L B a = (0 : ProdAdicCompletions B L)) := by
-- --             exact eq_zero_or_eq_zero_of_smul_eq_zero h
-- --           have : Function.Injective (ProdAdicCompletions.baseChange A K L B) := by
-- --             unfold baseChange
-- --             have inj': ∀(w: HeightOneSpectrum B),
-- --               Function.Injective (adicCompletionComapSemialgHom A K L B _ w rfl) := by
-- --               intro w
-- --               have h_inj : Function.Injective (algebraMap K L) :=
-- --                 RingHom.injective (algebraMap K L)
-- --               let inst_alg : Algebra (HeightOneSpectrum.adicCompletion K (comap A w))
-- --                 (HeightOneSpectrum.adicCompletion L w) := RingHom.toAlgebra <|
-- --                   adicCompletionComapSemialgHom A K L B (comap A w) w rfl
-- --               have inj: Function.Injective (algebraMap (HeightOneSpectrum.adicCompletion K (comap A w))
-- --                 (HeightOneSpectrum.adicCompletion L w)) :=
-- --                 RingHom.injective (algebraMap (HeightOneSpectrum.adicCompletion K (comap A w))
-- --                 (HeightOneSpectrum.adicCompletion L w))
-- --               intro x y hxy
-- --               have (z : HeightOneSpectrum.adicCompletion K (comap A w)):
-- --               (algebraMap (HeightOneSpectrum.adicCompletion K (comap A w))
-- --                 (HeightOneSpectrum.adicCompletion L w)) z =
-- --                 (adicCompletionComapSemialgHom A K L B (comap A w) w rfl) z :=
-- --                 rfl
-- --               rw [← this, ← this] at hxy
-- --               exact inj hxy
-- --             intro x y hxy
-- --             have (w: HeightOneSpectrum B) (x : ProdAdicCompletions A K): (adicCompletionComapSemialgHom A K L B _ w rfl)
-- --               (x (comap A w)) =
-- --               (Pi.semialgHomPi _ _ fun w ↦ adicCompletionComapSemialgHom A K L B (comap A w) w rfl)
-- --                x w := by
-- --               exact rfl
-- --             have (w: HeightOneSpectrum B) : (adicCompletionComapSemialgHom A K L B _ w rfl)
-- --               (x (comap A w)) = (adicCompletionComapSemialgHom A K L B _ w rfl)
-- --               (y (comap A w)) := by
-- --               rw [this, this]
-- --               exact congrFun hxy w
-- --             have this' (w: HeightOneSpectrum B) : (x (comap A w)) = (y (comap A w)) := inj' w (this w)
-- --             funext v
-- --             have : ∀(v: HeightOneSpectrum A), ∃(w: HeightOneSpectrum B), v = comap A w := by
-- --               intro v
-- --               sorry
-- --             obtain ⟨w, hw⟩ := this v
-- --             rw [hw]
-- --             exact this' w
-- --           rcases h₁ with (rfl | hba)
-- --           · rw [TensorProduct.zero_tmul]
-- --           · apply (map_eq_zero_iff _ this).mp at hba
-- --             rw [hba, TensorProduct.tmul_zero]
-- --         apply?
