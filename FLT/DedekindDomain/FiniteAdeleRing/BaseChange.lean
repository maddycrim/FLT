import Mathlib -- **TODO** fix when finished or if `exact?` is too slow
--import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
--import Mathlib.NumberTheory.NumberField.Basic
--import Mathlib.NumberTheory.RamificationInertia
import FLT.Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
import FLT.Mathlib.Algebra.Order.Hom.Monoid
import FLT.Mathlib.Algebra.Algebra.Subalgebra.Pi

/-!

# Base change of adele rings.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite separable
extension and if `B` is the integral closure of `A` in `L`, then `B` is also a Dedekind
domain. Hence the rings of finite adeles `𝔸_K^∞` and `𝔸_L^∞` (defined using `A` and `B`)
are defined. In this file we define the natural `K`-algebra map `𝔸_K^∞ → 𝔸_L^∞` and
the natural `L`-algebra map `𝔸_K^∞ ⊗[K] L → 𝔸_L^∞`, and show that the latter map
is an isomorphism.

## Main definition

* `FiniteAdeleRing.baseChangeEquiv : L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L`

-/

open scoped Multiplicative

-- The general set-up.

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L]

variable [Algebra.IsSeparable K L]

-- example : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
variable [IsDedekindDomain B]

-- example : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
variable [IsFractionRing B L]

-- example : IsDomain B := IsDomain.mk
variable [IsDomain B]

-- example : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
variable [Algebra.IsIntegral A B]

-- I can't find in mathlib the assertion that B is a finite A-module.
-- But it is!
example : Module.Finite A B := by
  have := IsIntegralClosure.isNoetherian A K L B
  exact Module.IsNoetherian.finite A B

-- We start by filling in some holes in the API for finite extensions of Dedekind domains.
namespace IsDedekindDomain

namespace HeightOneSpectrum

-- first need a way to pull back valuations on B to A
variable {B L} in
def comap (w : HeightOneSpectrum B) : HeightOneSpectrum A where
  asIdeal := w.asIdeal.comap (algebraMap A B)
  isPrime := Ideal.comap_isPrime (algebraMap A B) w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

lemma mk_count_factors_map
    (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (I : Ideal A) [DecidableEq (Associates (Ideal A))]
  [DecidableEq (Associates (Ideal B))] [∀ p : Associates (Ideal A), Decidable (Irreducible p)]
  [∀ p : Associates (Ideal B), Decidable (Irreducible p)] :
    (Associates.mk w.asIdeal).count (Associates.mk (Ideal.map (algebraMap A B) I)).factors =
    Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal *
      (Associates.mk (comap A w).asIdeal).count (Associates.mk I).factors := by
  classical
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Associates.mk_zero, Ideal.zero_eq_bot, Ideal.map_bot, ← Ideal.zero_eq_bot,
      Associates.mk_zero]
    simp [Associates.count, Associates.factors_zero, w.associates_irreducible,
      associates_irreducible (comap A w), Associates.bcount]
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp only [Submodule.zero_eq_bot, ne_eq, top_ne_bot, not_false_eq_true, Ideal.map_top]
    simp only [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
    rw [Associates.count_zero (associates_irreducible _),
      Associates.count_zero (associates_irreducible _), mul_zero]
  | h₃ I p hI hp IH =>
    simp only [Ideal.map_mul, ← Associates.mk_mul_mk]
    have hp_bot : p ≠ ⊥ := hp.ne_zero
    have hp_bot' := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hp_bot
    have hI_bot := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hI
    rw [Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot) (Associates.mk_ne_zero.mpr hI)
      (associates_irreducible _), Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot')
      (Associates.mk_ne_zero.mpr hI_bot) (associates_irreducible _)]
    simp only [IH, mul_add]
    congr 1
    by_cases hw : (w.comap A).asIdeal = p
    · have : Irreducible (Associates.mk p) := Associates.irreducible_mk.mpr hp.irreducible
      rw [hw, Associates.factors_self this, Associates.count_some this]
      simp only [UniqueFactorizationMonoid.factors_eq_normalizedFactors, Multiset.nodup_singleton,
        Multiset.mem_singleton, Multiset.count_eq_one_of_mem, mul_one]
      rw [count_associates_factors_eq hp_bot' w.2 w.3,
        Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp_bot' w.2 w.3]
    · have : (Associates.mk (comap A w).asIdeal).count (Associates.mk p).factors = 0 :=
        Associates.count_eq_zero_of_ne (associates_irreducible _)
          (Associates.irreducible_mk.mpr hp.irreducible)
          (by rwa [ne_eq, Associates.mk_eq_mk_iff_associated, associated_iff_eq])
      rw [this, mul_zero, eq_comm]
      by_contra H
      rw [eq_comm, ← ne_eq, Associates.count_ne_zero_iff_dvd hp_bot' (irreducible w),
        Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at H
      apply hw (((Ideal.isPrime_of_prime hp).isMaximal hp_bot).eq_of_le (comap A w).2.ne_top H).symm

lemma intValuation_comap (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (x : A) :
    (comap A w).intValuation x ^
    (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) =
    w.intValuation (algebraMap A B x) := by
  classical
  have h_ne_zero : Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero
      ((Ideal.map_eq_bot_iff_of_injective hAB).not.mpr (comap A w).3) w.2 Ideal.map_comap_le
  by_cases hx : x = 0
  · simpa [hx]
  simp only [intValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  show (ite _ _ _) ^ _ = ite _ _ _
  by_cases hx : x = 0
  · subst hx; simp [h_ne_zero]
  rw [map_eq_zero_iff _ hAB, if_neg hx, if_neg hx, ← Set.image_singleton, ← Ideal.map_span,
    mk_count_factors_map _ _ hAB, mul_comm]
  simp

-- Need to know how the valuation `w` and its pullback are related on elements of `K`.
omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
lemma valuation_comap (w : HeightOneSpectrum B) (x : K) :
    (comap A w).valuation x ^
    (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) =
    w.valuation (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation, ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
    ← intValuation_comap A B (algebraMap_injective_of_field_isFractionRing A B K L), div_pow]

variable {B L} in

/-- Say `w` is a finite place of `L` lying above `v` a finite place of `K`. Then there's a ring hom
`K_v → L_w`. -/
noncomputable def adicCompletionComapRingHom
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : v = comap A w) :
    adicCompletion K v →+* adicCompletion L w :=
  letI : UniformSpace K := v.adicValued.toUniformSpace;
  letI : UniformSpace L := w.adicValued.toUniformSpace;
  UniformSpace.Completion.mapRingHom (algebraMap K L) <| by
  -- question is the following:
  -- if L/K is a finite extension of sensible fields (e.g. number fields)
  -- and if w is a finite place of L lying above v a finite place of K,
  -- and if we give L the w-adic topology and K the v-adic topology,
  -- then the map K → L is continuous
  subst hvw
  refine continuous_of_continuousAt_zero (algebraMap K L) ?hf
  delta ContinuousAt
  simp only [map_zero]
  rw [(@Valued.hasBasis_nhds_zero K _ _ _ (comap A w).adicValued).tendsto_iff
    (@Valued.hasBasis_nhds_zero L _ _ _ w.adicValued)]
  simp only [HeightOneSpectrum.adicValued_apply, Set.mem_setOf_eq, true_and, true_implies]
  rw [WithZero.unitsWithZeroEquiv.forall_congr_left, Multiplicative.forall]
  intro a
  rw [WithZero.unitsWithZeroEquiv.exists_congr_left, Multiplicative.exists]
  let m := Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal
  let e : ℤ ≃ ℤₘ₀ˣ := Multiplicative.ofAdd.trans OrderMonoidIso.unitsWithZero.symm.toEquiv
  have e_apply (a : ℤ) : e a = OrderMonoidIso.unitsWithZero.symm (Multiplicative.ofAdd a) := rfl
  have hm : m ≠ 0 := by
    refine Ideal.IsDedekindDomain.ramificationIdx_ne_zero ?_ w.2 Ideal.map_comap_le
    exact (Ideal.map_eq_bot_iff_of_injective
      (algebraMap_injective_of_field_isFractionRing A B K L)).not.mpr (comap A w).3
  refine ⟨a / m, fun x hx ↦ ?_⟩
  simp_rw [← valuation_comap A]
  calc
    (comap A w).valuation x ^ m < e (a / ↑m) ^ m := by gcongr; exacts [zero_le', hx]
  _ = e (m • (a / ↑m)) := by
    dsimp [e]
    norm_cast
    rw [map_pow]
  _ ≤ e a := by
    simp only [nsmul_eq_mul, e_apply, Units.val_le_val, OrderIsoClass.map_le_map_iff]
    rw [mul_comm]
    exact Int.mul_le_of_le_ediv (by positivity) le_rfl

-- The below works!
--variable (w : HeightOneSpectrum B) in
--#synth SMul K (adicCompletion L w)

-- So we need to be careful making L_w into a K-algebra
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/beef.20up.20smul.20on.20completion.20to.20algebra.20instance/near/484166527
-- Hopefully resolved in https://github.com/leanprover-community/mathlib4/pull/19466
variable (w : HeightOneSpectrum B) in
noncomputable instance : Algebra K (adicCompletion L w) where
  toFun k := algebraMap L (adicCompletion L w) (algebraMap K L k)
  map_one' := by simp only [map_one]
  map_mul' k₁ k₂ := by simp only [map_mul]
  map_zero' := by simp only [map_zero]
  map_add' k₁ k₂ := by simp only [map_add]
  commutes' k lhat := mul_comm _ _
  smul_def' k lhat := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [UniformSpace.Completion.smul_def] -- not sure if this is the right move
    sorry -- surely true; issue #230

variable (w : HeightOneSpectrum B) in
instance : IsScalarTower K L (adicCompletion L w) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

noncomputable def adicCompletionComapAlgHom
  (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : v = comap A w) :
    (HeightOneSpectrum.adicCompletion K v) →A[K]
    (HeightOneSpectrum.adicCompletion L w) where
  __ := adicCompletionComapRingHom A K v w hvw
  commutes' r := by
    subst hvw
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    have : (adicCompletionComapRingHom A K _ w rfl) (algebraMap _ _ r)  =
        (algebraMap L (adicCompletion L w)) (algebraMap K L r) := by
      letI : UniformSpace L := w.adicValued.toUniformSpace
      letI : UniformSpace K := (comap A w).adicValued.toUniformSpace
      rw [adicCompletionComapRingHom, UniformSpace.Completion.mapRingHom]
      apply UniformSpace.Completion.extensionHom_coe
    rw [this, ← IsScalarTower.algebraMap_apply K L]
  cont :=
    letI : UniformSpace K := v.adicValued.toUniformSpace;
    letI : UniformSpace L := w.adicValued.toUniformSpace;
    UniformSpace.Completion.continuous_extension

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
lemma adicCompletionComapAlgHom_coe
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : v = comap A w) (x : K) :
    adicCompletionComapAlgHom A K L B v w hvw x = algebraMap K L x :=
  (adicCompletionComapAlgHom A K L B v w hvw).commutes _

-- this name is surely wrong
omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
open WithZeroTopology in
lemma v_adicCompletionComapAlgHom
  (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : v = comap A w) (x) :
    Valued.v (adicCompletionComapAlgHom A K L B v w hvw x) = Valued.v x ^
      Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal := by
  revert x
  apply funext_iff.mp
  symm
  letI : UniformSpace K := v.adicValued.toUniformSpace
  letI : UniformSpace L := w.adicValued.toUniformSpace
  apply UniformSpace.Completion.ext
  · exact Valued.continuous_valuation.pow _
  · exact Valued.continuous_valuation.comp (adicCompletionComapAlgHom ..).cont
  intro a
  simp only [Valued.valuedCompletion_apply, adicCompletionComapAlgHom_coe]
  show v.valuation a ^ _ = (w.valuation _)
  subst hvw
  rw [← valuation_comap A K L B w a]

noncomputable def adicCompletionComapAlgHom' (v : HeightOneSpectrum A) :
  (HeightOneSpectrum.adicCompletion K v) →ₐ[K]
    (∀ w : {w : HeightOneSpectrum B // v = comap A w}, HeightOneSpectrum.adicCompletion L w.1) :=
  Pi.algHom _ _ fun i ↦ adicCompletionComapAlgHom A K L B v i.1 i.2

noncomputable def adicCompletionContinuousComapAlgHom (v : HeightOneSpectrum A) :
  (HeightOneSpectrum.adicCompletion K v) →A[K]
    (∀ w : {w : HeightOneSpectrum B // v = comap A w}, HeightOneSpectrum.adicCompletion L w.1) where
  __ := adicCompletionComapAlgHom' A K L B v
  cont := continuous_pi fun w ↦ (adicCompletionComapAlgHom A K L B v _ w.2).cont

open scoped TensorProduct -- ⊗ notation for tensor product

noncomputable def adicCompletionTensorComapAlgHom (v : HeightOneSpectrum A) :
    L ⊗[K] adicCompletion K v →ₐ[L]
      Π w : {w : HeightOneSpectrum B // v = comap A w}, adicCompletion L w.1 :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (adicCompletionComapAlgHom' A K L B v) fun _ _ ↦ .all _ _

lemma adicCompletionComapAlgIso_tmul_apply (v : HeightOneSpectrum A) (x y i) :
  adicCompletionTensorComapAlgHom A K L B v (x ⊗ₜ y) i =
    x • adicCompletionComapAlgHom A K L B v i.1 i.2 y := by
  rw [Algebra.smul_def]
  rfl

attribute [local instance 9999] SMulCommClass.of_commMonoid TensorProduct.isScalarTower_left IsScalarTower.right

instance (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    IsScalarTower R (adicCompletionIntegers K v) (adicCompletion K v) :=
  ⟨fun x y z ↦ by exact smul_mul_assoc x y.1 z⟩

noncomputable
def adicCompletionIntegersSubalgebra {R : Type*} (K : Type*) [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    Subalgebra R (HeightOneSpectrum.adicCompletion K v) where
  __ := HeightOneSpectrum.adicCompletionIntegers K v
  algebraMap_mem' r := coe_mem_adicCompletionIntegers v r

noncomputable def tensorAdicCompletionIntegersTo (v : HeightOneSpectrum A) :
    B ⊗[A] adicCompletionIntegers K v →ₐ[B] L ⊗[K] adicCompletion K v :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft).comp (Algebra.ofId B L))
    ((Algebra.TensorProduct.includeRight.restrictScalars A).comp (IsScalarTower.toAlgHom _ _ _))
    (fun _ _ ↦ .all _ _)

set_option linter.deprecated false in -- `map_zero` and `map_add` time-outs
theorem range_adicCompletionComapAlgIso_tensorAdicCompletionIntegersTo_le_pi
    (v : HeightOneSpectrum A) :
    AlgHom.range (((adicCompletionTensorComapAlgHom A K L B v).restrictScalars B).comp
      (tensorAdicCompletionIntegersTo A K L B v)) ≤
      Subalgebra.pi Set.univ (fun _ ↦ adicCompletionIntegersSubalgebra _ _) := by
  rintro _ ⟨x, rfl⟩ i -
  simp only [Subalgebra.coe_toSubmodule, AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.coe_comp, AlgHom.coe_restrictScalars', AlgHom.coe_coe,
    Function.comp_apply, SetLike.mem_coe]
  induction' x with x y x y hx hy
  · rw [(tensorAdicCompletionIntegersTo A K L B v).map_zero,
      (adicCompletionTensorComapAlgHom A K L B v).map_zero]
    exact zero_mem _
  · simp only [tensorAdicCompletionIntegersTo, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
      Function.comp_apply, Algebra.ofId_apply, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, AlgHom.coe_restrictScalars',
      IsScalarTower.coe_toAlgHom', ValuationSubring.algebraMap_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      adicCompletionComapAlgIso_tmul_apply, algebraMap_smul]
    apply Subalgebra.smul_mem
    show _ ≤ (1 : ℤₘ₀)
    rw [v_adicCompletionComapAlgHom A K (L := L) (B := B) v i.1 i.2 y.1,
      ← one_pow (Ideal.ramificationIdx (algebraMap A B) (comap A i.1).asIdeal i.1.asIdeal),
      pow_le_pow_iff_left₀]
    · exact y.2
    · exact zero_le'
    · exact zero_le'
    · exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero  ((Ideal.map_eq_bot_iff_of_injective
        (algebraMap_injective_of_field_isFractionRing A B K L)).not.mpr
        (comap A i.1).3) i.1.2 Ideal.map_comap_le
  · rw [(tensorAdicCompletionIntegersTo A K L B v).map_add,
      (adicCompletionTensorComapAlgHom A K L B v).map_add]
    exact add_mem hx hy

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
variable (v : HeightOneSpectrum A) in
instance : TopologicalSpace (L ⊗[K] adicCompletion K v) := moduleTopology (adicCompletion K v) _

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
variable (v : HeightOneSpectrum A) in
instance : IsModuleTopology (adicCompletion K v) (L ⊗[K] adicCompletion K v) :=
  ⟨rfl⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
noncomputable def adicCompletionTensorComapContinuousAlgHom (v : HeightOneSpectrum A) :
    L ⊗[K] adicCompletion K v →A[L]
      Π w : {w : HeightOneSpectrum B // v = comap A w}, adicCompletion L w.1 where
  __ := adicCompletionTensorComapAlgHom A K L B v
  cont := by
    apply IsModuleTopology.continuous_of_ringHom (R := adicCompletion K v)
    show Continuous (RingHom.comp _ (Algebra.TensorProduct.includeRight.toRingHom))
    convert (adicCompletionContinuousComapAlgHom A K L B v).cont using 1
    ext
    simp [adicCompletionTensorComapAlgHom, adicCompletionContinuousComapAlgHom]

noncomputable def adicCompletionComapAlgEquiv (v : HeightOneSpectrum A) :
  (L ⊗[K] (HeightOneSpectrum.adicCompletion K v)) ≃ₐ[L]
    (∀ w : {w : HeightOneSpectrum B // v = comap A w}, HeightOneSpectrum.adicCompletion L w.1) :=
  AlgEquiv.ofBijective (adicCompletionTensorComapAlgHom A K L B v) sorry --#231

-- Can't state this properly because ≃[A]L doesn't exist yet -- #238
noncomputable def adicCompletionComapContinuousAlgEquiv (v : HeightOneSpectrum A) :
  sorry
--  (L ⊗[K] (HeightOneSpectrum.adicCompletion K v)) ≃A[L]
--    (∀ w : {w : HeightOneSpectrum B // v = comap A w}, HeightOneSpectrum.adicCompletion L w.1)
  := sorry

theorem adicCompletionComapAlgEquiv_integral : ∃ S : Finset (HeightOneSpectrum A), ∀ v ∉ S,
  AlgHom.range (((adicCompletionTensorComapAlgHom A K L B v).restrictScalars B).comp
      (tensorAdicCompletionIntegersTo A K L B v)) =
      Subalgebra.pi Set.univ (fun _ ↦ adicCompletionIntegersSubalgebra _ _) := sorry

end IsDedekindDomain.HeightOneSpectrum

namespace DedekindDomain

open IsDedekindDomain HeightOneSpectrum

open scoped TensorProduct -- ⊗ notation for tensor product

-- Make ∏_w L_w into a K-algebra in a way compatible with the L-algebra structure
variable [Algebra K (ProdAdicCompletions B L)]
  [IsScalarTower K L (ProdAdicCompletions B L)]

noncomputable def ProdAdicCompletions.baseChange :
    ProdAdicCompletions A K →ₐ[K] ProdAdicCompletions B L where
  toFun kv w := (adicCompletionComapAlgHom A K L B _ w rfl (kv (comap A w)))
  map_one' := by
    dsimp only
    exact funext fun w => by rw [Pi.one_apply, Pi.one_apply, map_one]
  map_mul' x y := by
    dsimp only
    exact funext fun w => by rw [Pi.mul_apply, Pi.mul_apply, map_mul]
  map_zero' := by
    dsimp only
    exact funext fun w => by rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  map_add' x y := by
    dsimp only
    funext w
    letI : Module K (adicCompletion L w) := Algebra.toModule
    rw [Pi.add_apply, Pi.add_apply, map_add]
  commutes' r := by
    funext w
    rw [IsScalarTower.algebraMap_apply K L (ProdAdicCompletions B L)]
    dsimp only [algebraMap_apply']
    exact adicCompletionComapAlgHom_coe A K L B _ w _ r

variable {R : Type*} [CommRing R]
variable {ι : Type*}
variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- def submodule (L : Type*) [AddCommGroup L] [Module R L] (K : Submodule R L) :  Submodule R (L ⊗[R] M) := sorry

open DirectSum

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
       --unfold TensorProduct.lift at h
       sorry
     sorry
   · sorry

noncomputable def ProdAdicCompletions.baseChangeEquiv :
    L ⊗[K] ProdAdicCompletions A K ≃ₐ[L] ProdAdicCompletions B L := by
  --can I get around constructing an explicit map?
  have h₄: (∀(v: HeightOneSpectrum A), (∀ w : {w : HeightOneSpectrum B // v = comap A w}, HeightOneSpectrum.adicCompletion L w.1))
    ≃ₐ[L] ProdAdicCompletions B L :=
    {
    toFun := fun f w ↦ f (comap A w) ⟨w, rfl⟩
    invFun := fun g v w ↦ g w
    -- better way to prove left_inv?
    left_inv := fun f ↦ by
      ext v w₁
      simp
      congr
      exact w₁.2.symm
      ext w₂
      refine Eq.congr ?_ rfl
      exact w₁.2.symm
      exact proof_irrel_heq rfl w₁.property
    right_inv := fun g ↦ rfl
    map_mul' := fun x y ↦ rfl
    map_add' := fun x y ↦ rfl
    commutes' := fun r ↦ rfl
   }
  have h₆ : L ⊗[K] ((i : HeightOneSpectrum A) → adicCompletion K i) ≃ₐ[L]
    (i : HeightOneSpectrum A) → L ⊗[K] adicCompletion K i := by
    use tensorProdbilinear (R:=K) (M := L) (N:= (adicCompletion K (R:= A)))
    · sorry
    · exact tensorProdbilinear.map_add
    · intro r
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      rw [Algebra.TensorProduct.one_def]
      rw [TensorProduct.smul_tmul']
      simp only [smul_eq_mul, mul_one]
      simp only [Equiv.toFun_as_coe, EquivLike.coe_coe]
      refine funext ?_
      intro v
      haveI (i : HeightOneSpectrum A) := AddCommMonoid (adicCompletion K i)
      have : tensorProdbilinear (r ⊗ₜ[K] 1) v = (r ⊗ₜ[K] (1: adicCompletion K v)) := rfl
      rw [this, ← mul_one r, ← smul_eq_mul, ← TensorProduct.smul_tmul',
        ← Algebra.TensorProduct.one_def]
      simp only [smul_eq_mul, mul_one, Pi.smul_apply, Pi.one_apply]

  have h₇ : ((v : HeightOneSpectrum A) → L ⊗[K] adicCompletion K v )≃ₐ[L]
    (v: HeightOneSpectrum A) → (∀ w : {w : HeightOneSpectrum B // v = comap A w}, HeightOneSpectrum.adicCompletion L w.1) :=
    AlgEquiv.piCongrRight (fun (v: HeightOneSpectrum A) ↦ adicCompletionComapAlgEquiv A K L B v)
  exact (h₆.trans h₇).trans h₄
    -- letI : SMulCommClass K ((i : HeightOneSpectrum A) → adicCompletion K i)
    --   ((i : HeightOneSpectrum A) → adicCompletion K i) := by
    --   exact Pi.smulCommClass'
    -- letI : NonUnitalSemiring (L ⊗[K] ((i : HeightOneSpectrum A) → adicCompletion K i)) := by
    --   exact Algebra.TensorProduct.instNonUnitalSemiring
    -- have :=(LinearEquiv.toLinearMap (tensorProdbilinear (R:=K) (M := L)
    --   (N:= (adicCompletion K (R:= A))))).map_mul_iff (R:= K)


     #exit




-- I am unclear about whether these next two sorries are in the right order.
-- One direction of `baseChange_isFiniteAdele_iff` below (->) is easy, but perhaps the other way
-- should be deduced from the result after this one. See #240.
-- (`ProdAdicCompletions.baseChangeEquiv_isFiniteAdele_iff`).
theorem ProdAdicCompletions.baseChange_isFiniteAdele_iff
    (x : ProdAdicCompletions A K) :
    ProdAdicCompletions.IsFiniteAdele x ↔
    ProdAdicCompletions.IsFiniteAdele (ProdAdicCompletions.baseChange A K L B x) := sorry --#240

-- This theorem and the one before are probably equivalent, I'm not sure which one to prove first.
-- See #240
theorem ProdAdicCompletions.baseChangeEquiv_isFiniteAdele_iff
    (x : ProdAdicCompletions A K) :
    ProdAdicCompletions.IsFiniteAdele x ↔
    ProdAdicCompletions.IsFiniteAdele (ProdAdicCompletions.baseChangeEquiv A K L B (1 ⊗ₜ x)) :=
  sorry -- #240

-- Easy consequence of the previous result
theorem ProdAdicCompletions.baseChangeEquiv_isFiniteAdele_iff'
    (x : ProdAdicCompletions A K) :
    ProdAdicCompletions.IsFiniteAdele x ↔
    ∀ (l : L), ProdAdicCompletions.IsFiniteAdele
      (ProdAdicCompletions.baseChangeEquiv A K L B (l ⊗ₜ x)) := sorry -- #241

-- Make ∏_w L_w into a K-algebra in a way compatible with the L-algebra structure
variable [Algebra K (FiniteAdeleRing B L)]
  [IsScalarTower K L (FiniteAdeleRing B L)]

-- Restriction of an algebra map is an algebra map; these should be easy. #242
noncomputable def FiniteAdeleRing.baseChange : FiniteAdeleRing A K →ₐ[K] FiniteAdeleRing B L where
  toFun ak := ⟨ProdAdicCompletions.baseChange A K L B ak.1,
    (ProdAdicCompletions.baseChange_isFiniteAdele_iff A K L B ak).1 ak.2⟩
  map_one' := by
    ext
    have h : (1 : FiniteAdeleRing A K) = (1 : ProdAdicCompletions A K) := rfl
    have t : (1 : FiniteAdeleRing B L) = (1 : ProdAdicCompletions B L) := rfl
    simp_rw [h, t, map_one]
  map_mul' x y := by
    have h : (x * y : FiniteAdeleRing A K) =
      (x : ProdAdicCompletions A K) * (y : ProdAdicCompletions A K) := rfl
    simp_rw [h, map_mul]
    rfl
  map_zero' := by
    ext
    have h : (0 : FiniteAdeleRing A K) = (0 : ProdAdicCompletions A K) := rfl
    have t : (0 : FiniteAdeleRing B L) = (0 : ProdAdicCompletions B L) := rfl
    simp_rw [h, t, map_zero]
  map_add' x y:= by
    have h : (x + y : FiniteAdeleRing A K) =
      (x : ProdAdicCompletions A K) + (y : ProdAdicCompletions A K) := rfl
    simp_rw [h, map_add]
    rfl
  commutes' r := by
    ext
    have h : (((algebraMap K (FiniteAdeleRing A K)) r) : ProdAdicCompletions A K) =
      (algebraMap K (ProdAdicCompletions A K)) r := rfl
    have i : algebraMap K (FiniteAdeleRing B L) r =
      algebraMap L (FiniteAdeleRing B L) (algebraMap K L r) :=
      IsScalarTower.algebraMap_apply K L (FiniteAdeleRing B L) r
    have j (p : L) : (((algebraMap L (FiniteAdeleRing B L)) p) : ProdAdicCompletions B L) =
      (algebraMap L (ProdAdicCompletions B L)) p := rfl
    simp_rw [h, AlgHom.commutes, i, j]
    exact IsScalarTower.algebraMap_apply K L (ProdAdicCompletions B L) r

-- Presumably we have this?
noncomputable def bar {K L AK AL : Type*} [CommRing K] [CommRing L]
    [CommRing AK] [CommRing AL] [Algebra K AK] [Algebra K AL] [Algebra K L]
    [Algebra L AL] [IsScalarTower K L AL]
    (f : AK →ₐ[K] AL) : L ⊗[K] AK →ₐ[L] AL :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) f <| fun l ak ↦ mul_comm (Algebra.ofId _ _ l) (f ak)

-- Follows from the above. Should be a continuous L-alg equiv but we don't have continuous
-- alg equivs yet so can't even state it properly.
noncomputable def FiniteAdeleRing.baseChangeEquiv : L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L :=
  AlgEquiv.ofBijective (bar <| FiniteAdeleRing.baseChange A K L B) sorry -- #243

end DedekindDomain
