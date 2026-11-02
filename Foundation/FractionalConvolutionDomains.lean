import Foundation.FractionalMAHorizon
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! Actual convolution-profile L2 continuity and local weighted Bochner domains.
The original predictable integral/source derivative and finite-horizon support
are preserved; canonical stochastic step-limit identification is separate. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalConvolutionDomains
open OperatorDerivativeRewrite.Foundation GaussianTimeHilbert GaussianDeterministicVolterra
attribute [local instance] timeHilbert_secondCountable
local instance : CompleteSpace positiveProfiles :=
  (show IsClosed (positiveProfiles : Set TimeHilbert) from
    supportedL2_isClosed (μ := (volume : Measure ℝ)) measurableSet_Ioi).completeSpace_coe

def translation (a : ℝ) : C(ℝ,ℝ) := ⟨fun x => x+a,continuous_id.add_const a⟩

theorem translation_continuous : Continuous translation := by
 apply ContinuousMap.continuous_of_continuous_uncurry
 change Continuous (fun p : ℝ×ℝ => p.2+p.1)
 exact continuous_snd.add continuous_fst

def translated (a : ℝ) (f : TimeHilbert) : TimeHilbert :=
 Lp.compMeasurePreserving (translation a) (measurePreserving_add_right (volume : Measure ℝ) a) f

theorem translated_continuous (f : TimeHilbert) : Continuous (fun a => translated a f) := by
 exact continuous_const.compMeasurePreservingLp translation_continuous
   (fun a => measurePreserving_add_right (volume : Measure ℝ) a) (by norm_num)

theorem translated_coeFn (a : ℝ) (f : TimeHilbert) : translated a f =ᵐ[volume] fun x => f (x+a) := by
 simpa only [translated,translation,ContinuousMap.coe_mk,Function.comp_def] using
   Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right (volume : Measure ℝ) a)

section Convolution

variable (K : ℝ≥0 → TimeHilbert) (k : ℝ → ℝ)
 (hK : ∀ t, K t =ᵐ[volume] (Ioc 0 (t:ℝ)).indicator (fun x => k ((t:ℝ)-x)))

include hK

theorem convolution_mem_positive (t : ℝ≥0) : K t ∈ positiveProfiles := by
 rw [positiveProfiles,mem_supportedL2_iff measurableSet_Ioi]
 filter_upwards [hK t] with x hx hn
 rw [hx]
 exact indicator_of_notMem (fun h => hn h.1) _

theorem convolution_projection (t S : ℝ≥0) (ht : t≤S) :
 positiveProfiles.starProjection (translated ((S:ℝ)-t) (K S)) = K t := by
 have hmem := convolution_mem_positive K k hK t
 apply positiveProfiles.eq_starProjection_of_mem_of_inner_eq_zero hmem
 intro w hw
 rw [L2_inner_eq_integral]
 apply integral_eq_zero_of_ae
 have hw0 := (mem_supportedL2_iff measurableSet_Ioi w).mp hw
 have hS := (measurePreserving_add_right (volume : Measure ℝ) ((S:ℝ)-t)).quasiMeasurePreserving.ae (hK S)
 filter_upwards [Lp.coeFn_sub (translated ((S:ℝ)-t) (K S)) (K t),
   translated_coeFn ((S:ℝ)-t) (K S),hK t,hS,hw0] with x hd hs ht' hS hw'
 change inner ℝ ((translated ((S:ℝ)-t) (K S)-K t) x) (w x)=0
 rw [hd]
 change inner ℝ (translated ((S:ℝ)-t) (K S) x-K t x) (w x)=0
 rw [hs,ht',hS]
 by_cases hx : 0<x
 · by_cases hxt : x≤(t:ℝ)
   · have hit : x∈Ioc 0 (t:ℝ) := ⟨hx,hxt⟩
     have hiS : x+((S:ℝ)-t)∈Ioc 0 (S:ℝ) := by
       constructor <;> have htt : (t:ℝ)≤S := ht <;> linarith
     rw [indicator_of_mem hit,indicator_of_mem hiS,
       show (S:ℝ)-(x+((S:ℝ)-t))=(t:ℝ)-x by ring,sub_self,inner_zero_left]
   · have hit : x∉Ioc 0 (t:ℝ) := fun h => hxt h.2
     have hiS : x+((S:ℝ)-t)∉Ioc 0 (S:ℝ) := by intro h; apply hxt; linarith [h.2]
     simp [indicator_of_notMem hit,indicator_of_notMem hiS]
 · have hwz : w x=0 := hw' (by simpa using hx)
   simp [hwz]

theorem convolution_continuous : Continuous K := by
 apply continuous_iff_continuousAt.mpr
 intro t0
 let S : ℝ≥0 := t0+1
 have ht0 : t0<S := by dsimp [S]; exact lt_add_of_pos_right _ zero_lt_one
 let F : ℝ≥0 → TimeHilbert := fun t => positiveProfiles.starProjection (translated ((S:ℝ)-t) (K S))
 have hc : Continuous F := positiveProfiles.starProjection.continuous.comp
   ((translated_continuous (K S)).comp (continuous_const.sub NNReal.continuous_coe))
 have he : F =ᶠ[nhds t0] K := by
   filter_upwards [eventually_lt_nhds ht0] with t ht
   exact convolution_projection K k hK t S ht.le
 have hz : F t0=K t0 := convolution_projection K k hK t0 S ht0.le
 have hh : Tendsto F (nhds t0) (nhds (K t0)) := by
   rw [← hz]
   exact hc.continuousAt.tendsto
 exact hh.congr' he

theorem convolution_weighted_integrable (q : ℝ → ℝ) (a b : ℝ)
 (hq : ContinuousOn q (uIcc a b)) :
 IntervalIntegrable (fun s : ℝ => q s • K s.toNNReal) volume a b :=
 (hq.smul (((convolution_continuous K k hK).comp continuous_real_toNNReal).continuousOn)).intervalIntegrable

theorem convolution_weighted_positive (f q : ℝ → ℝ) (T : ℝ≥0) (hq : ContinuousOn q (Icc 0 (T:ℝ))) :
 FractionalNoisingTransfer.weightedVector (fun s : ℝ => K s.toNNReal) f q T ∈ positiveProfiles := by
 rw [← Submodule.starProjection_eq_self_iff]
 have hfix (s : ℝ≥0) : positiveProfiles.starProjection (K s)=K s :=
   Submodule.starProjection_eq_self_iff.mpr (convolution_mem_positive K k hK s)
 rw [FractionalNoisingTransfer.weightedVector,map_sub,map_smul,Real.toNNReal_coe,hfix]
 congr 1
 rw [← positiveProfiles.starProjection.intervalIntegral_comp_comm
   (convolution_weighted_integrable K k hK q 0 T (by simpa only [uIcc_of_le T.coe_nonneg] using hq))]
 apply intervalIntegral.integral_congr
 intro s _
 dsimp only
 rw [map_smul,hfix]

theorem convolution_weighted_horizon (f q : ℝ → ℝ) (T : ℝ≥0) (hq : ContinuousOn q (Icc 0 (T:ℝ))) :
 FractionalNoisingTransfer.weightedVector (fun s : ℝ => K s.toNNReal) f q T ∈
   supportedL2 (μ := (volume : Measure ℝ)) (s := Ioc 0 (T:ℝ)) measurableSet_Ioc := by
 let Q := supportedL2 (μ := (volume : Measure ℝ)) (s := Ioc 0 (T:ℝ)) measurableSet_Ioc
 let : CompleteSpace Q := (supportedL2_isClosed (μ := (volume : Measure ℝ))
   (s := Ioc 0 (T:ℝ)) measurableSet_Ioc).completeSpace_coe
 have hmem (u : ℝ≥0) (hu : u≤T) : K u ∈ Q := by
   change K u ∈ supportedL2 (μ := (volume : Measure ℝ)) (s := Ioc 0 (T:ℝ)) measurableSet_Ioc
   rw [mem_supportedL2_iff measurableSet_Ioc]
   filter_upwards [hK u] with x hx hn
   rw [hx]
   exact indicator_of_notMem (fun h => hn ⟨h.1,h.2.trans hu⟩) _
 change FractionalNoisingTransfer.weightedVector (fun s : ℝ => K s.toNNReal) f q T ∈ Q
 rw [← Submodule.starProjection_eq_self_iff]
 have ht : Q.starProjection (K T)=K T := Submodule.starProjection_eq_self_iff.mpr (hmem T le_rfl)
 rw [FractionalNoisingTransfer.weightedVector,map_sub,map_smul,Real.toNNReal_coe,ht]
 congr 1
 rw [← Q.starProjection.intervalIntegral_comp_comm
   (convolution_weighted_integrable K k hK q 0 T (by simpa only [uIcc_of_le T.coe_nonneg] using hq))]
 apply intervalIntegral.integral_congr
 intro u hu
 rw [uIcc_of_le T.coe_nonneg] at hu
 have hut : u.toNNReal≤T := by
   change (u.toNNReal:ℝ)≤T
   rw [Real.coe_toNNReal u hu.1]
   exact hu.2
 dsimp only
 rw [map_smul,Submodule.starProjection_eq_self_iff.mpr (hmem u.toNNReal hut)]

theorem convolution_weighted_native_input (f q : ℝ → ℝ) (T : ℝ≥0) (hq : ContinuousOn q (Icc 0 (T:ℝ))) :
 GaussianTimeProductL2.productTensor
   (FractionalNoisingTransfer.weightedVector (fun s : ℝ => K s.toNNReal) f q T)
   InfiniteGaussian.gaussianOne ∈ GaussianPredictableFull.fullPredictable := by
 apply positive_profile_predictable
 have hm := convolution_weighted_positive K k hK f q T hq
 have hs := (mem_supportedL2_iff measurableSet_Ioi _).mp hm
 filter_upwards [hs] with x hx hnon
 exact hx (not_lt.mpr hnon)

theorem convolution_weighted_native_integral (f q : ℝ → ℝ) (T : ℝ≥0) (hq : ContinuousOn q (Icc 0 (T:ℝ))) :
 GaussianPredictableFull.itoIntegral
   ⟨GaussianTimeProductL2.productTensor
     (FractionalNoisingTransfer.weightedVector (fun s : ℝ => K s.toNNReal) f q T)
     InfiniteGaussian.gaussianOne,convolution_weighted_native_input K k hK f q T hq⟩ =
   FractionalNoisingTransfer.weightedObservable (fun s : ℝ => K s.toNNReal) f q T := by
 rw [FractionalNoisingTransfer.weighted_realization _ _ _ _
   (convolution_weighted_integrable K k hK q 0 T (by simpa only [uIcc_of_le T.coe_nonneg] using hq))]
 exact GaussianDeterministicIntegral.itoIntegral_deterministic _ _

theorem convolution_weighted_source_derivative (f q : ℝ → ℝ) (T : ℝ≥0) (hq : ContinuousOn q (Icc 0 (T:ℝ))) :
 (FractionalNoisingTransfer.weightedObservable (fun s : ℝ => K s.toNNReal) f q T,
   GaussianContinuousRigidity.fieldEmbedding (GaussianTimeProductL2.productTensor
     (FractionalNoisingTransfer.weightedVector (fun s : ℝ => K s.toNNReal) f q T)
     InfiniteGaussian.gaussianOne)) ∈ InfiniteGaussian.closedCylindricalDerivative.graph :=
 FractionalNoisingTransfer.weighted_closed_derivative _ f q T
   (convolution_weighted_integrable K k hK q 0 T (by simpa only [uIcc_of_le T.coe_nonneg] using hq))

end Convolution

open FractionalMAHorizon

theorem typeII_vector_continuous (H : ℝ) (hH : 0<H) : Continuous (targetVector H hH) :=
 convolution_continuous _ (targetLag H) (targetVector_coeFn H hH)

theorem ma_vector_continuous (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0) :
 Continuous (maVector n w rate) :=
 convolution_continuous _ (maLag n w rate) (maVector_coeFn n w rate)

theorem typeII_weighted_integrable (H : ℝ) (hH : 0<H) (q : ℝ → ℝ) (a b : ℝ) (hq : ContinuousOn q (uIcc a b)) :
 IntervalIntegrable (fun s : ℝ => q s • targetVector H hH s.toNNReal) volume a b :=
 convolution_weighted_integrable _ (targetLag H) (targetVector_coeFn H hH) q a b hq

theorem ma_weighted_integrable (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (q : ℝ → ℝ) (a b : ℝ) (hq : ContinuousOn q (uIcc a b)) :
 IntervalIntegrable (fun s : ℝ => q s • maVector n w rate s.toNNReal) volume a b :=
 convolution_weighted_integrable _ (maLag n w rate) (maVector_coeFn n w rate) q a b hq

theorem typeII_observable_continuous (H : ℝ) (hH : 0<H) :
 Continuous (FractionalNoisingTransfer.typeII H hH) :=
 (GaussianHilbertProcess.isonormalEmbedding TimeHilbert).continuous.comp (typeII_vector_continuous H hH)

theorem weighted_interior_convergence_continuous (N : ℕ → ℕ)
 (w : (m : ℕ) → Fin (N m) → ℝ) (rate : (m : ℕ) → Fin (N m) → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t S : ℝ≥0) (ht : t<S) (f q : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 (t:ℝ)))
 (havg : Tendsto (fun m => ∫ s in (0:ℝ)..(S:ℝ),
   ‖errorObservable (N m) (w m) (rate m) H hH s.toNNReal‖^2) atTop (nhds 0)) :
 Tendsto (fun m => FractionalNoisingTransfer.weightedObservable
   (fun s : ℝ => maVector (N m) (w m) (rate m) s.toNNReal) f q t) atTop
   (nhds (FractionalNoisingTransfer.weightedObservable
     (fun s : ℝ => targetVector H hH s.toNNReal) f q t)) := by
 obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
 have hM0 : 0≤M := (norm_nonneg (q 0)).trans (hM 0 ⟨le_rfl,t.coe_nonneg⟩)
 apply weighted_actual_interior_convergence N w rate H hH t S ht f q
   (fun m => ma_weighted_integrable (N m) (w m) (rate m) q 0 t (by simpa only [uIcc_of_le t.coe_nonneg] using hq))
   (typeII_weighted_integrable H hH q 0 t (by simpa only [uIcc_of_le t.coe_nonneg] using hq)) M hM0 _ havg
 intro s hs
 simpa only [Real.norm_eq_abs] using hM s hs

end OperatorDerivativeRewrite.Foundation.FractionalConvolutionDomains
