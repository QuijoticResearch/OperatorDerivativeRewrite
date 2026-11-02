import Foundation.FractionalNoisingTopology
import Foundation.GaussianExponentialMarkovPrediction
/-! Actual finite shared-Brownian MA-OU versus Gamma-normalized Type-II noising:
interior convergence from averaged error, original native integral and derivative,
and a sharp endpoint trace obstruction in a larger Gaussian Volterra class. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalMAHorizon
open OperatorDerivativeRewrite.Foundation InfiniteGaussian GaussianPowerVolterra GaussianTimeHilbert
attribute [local instance] timeHilbert_secondCountable

def spike (n : ℕ) (t : ℝ≥0) : GaussianL2 :=
 Real.sqrt (2*(n:ℝ)+1) • value (n:ℝ) (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith) t

theorem spike_energy (n : ℕ) (t : ℝ≥0) : ‖spike n t‖^2 = (t : ℝ)^(2*(n:ℝ)+1) := by
 rw [spike,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by positivity)]
 rw [value,GaussianDeterministicVolterra.profileIntegral_eq_isonormal]
 change (2*(n:ℝ)+1) * ‖GaussianHilbertProcess.isonormalEmbedding TimeHilbert
   (vector (n:ℝ) (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith) t)‖^2 = _
 rw [LinearIsometry.norm_map, vector_norm_sq]
 field_simp

theorem spike_endpoint (n : ℕ) : ‖spike n 1‖^2 = 1 := by
 rw [spike_energy]
 simp

theorem spike_time_energy (n : ℕ) :
 (∫ s in (0:ℝ)..1, ‖spike n s.toNNReal‖^2) = 1/(2*(n:ℝ)+2) := by
 have he : (∫ s in (0:ℝ)..1, ‖spike n s.toNNReal‖^2) =
     ∫ s in (0:ℝ)..1, s^(2*(n:ℝ)+1) := by
   apply intervalIntegral.integral_congr
   intro s hs
   rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hs
   change ‖spike n s.toNNReal‖^2 = s^(2*(n:ℝ)+1)
   rw [spike_energy,Real.coe_toNNReal s hs.1]
 rw [he,integral_rpow (Or.inl (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith : -1 < 2*(n:ℝ)+1))]
 simp only [Real.one_rpow,Real.zero_rpow (by positivity : 2*(n:ℝ)+1+1≠0),sub_zero]
 ring

theorem spike_time_energy_tendsto :
 Tendsto (fun n : ℕ => ∫ s in (0:ℝ)..1, ‖spike n s.toNNReal‖^2) atTop (nhds 0) := by
 have h : Tendsto (fun n : ℕ => (1/2:ℝ)*(1/((n:ℝ)+1))) atTop (nhds 0) := by
   simpa only [mul_zero] using
     ((tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))) :
       Tendsto (fun n : ℕ => (1/2:ℝ)*(1/((n:ℝ)+1))) atTop (nhds ((1/2:ℝ)*0)))
 convert h using 1
 funext n
 rw [spike_time_energy]
 field_simp

theorem no_uniform_endpoint_energy_bound (C : ℝ) : ∃ n : ℕ,
 C*(∫ s in (0:ℝ)..1, ‖spike n s.toNNReal‖^2) < ‖spike n 1‖^2 := by
 have hc : Tendsto (fun n : ℕ => C*(∫ s in (0:ℝ)..1, ‖spike n s.toNNReal‖^2))
     atTop (nhds 0) := by
   simpa only [mul_zero] using tendsto_const_nhds.mul spike_time_energy_tendsto
 obtain ⟨n,hn⟩ := (hc.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))).exists
 exact ⟨n,by simpa only [spike_endpoint] using hn⟩


def maLag (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0) (u : ℝ) : ℝ :=
 ∑ i, w i * Real.exp (-(rate i : ℝ)*u)

def targetLag (H u : ℝ) : ℝ := (Real.Gamma (H+1/2))⁻¹ * u^(H-1/2)
def lagError (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0) (H u : ℝ) : ℝ :=
 maLag n w rate u-targetLag H u

def maVector (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0) (t : ℝ≥0) : TimeHilbert :=
 ∑ i, w i • SPDEExponentialForcing.responseVector (rate i) t

def targetVector (H : ℝ) (hH : 0<H) (t : ℝ≥0) : TimeHilbert :=
 FractionalForcingKernel.responseVector (H+1/2) (by linarith) t

def errorVector (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t : ℝ≥0) : TimeHilbert :=
 maVector n w rate t-targetVector H hH t

def errorObservable (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t : ℝ≥0) : GaussianL2 :=
 GaussianHilbertProcess.isonormalEmbedding TimeHilbert (errorVector n w rate H hH t)

theorem actual_error (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t : ℝ≥0) :
 errorObservable n w rate H hH t =
 (∑ i, w i • GaussianExponentialMarkovPrediction.value (rate i) t)-
   FractionalNoisingTransfer.typeII H hH t := by
 rw [errorObservable,errorVector,map_sub,maVector,map_sum]
 congr 1
 apply Finset.sum_congr rfl
 intro i _
 rw [map_smul]
 rfl

theorem maVector_coeFn (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0) (t : ℝ≥0) :
 maVector n w rate t =ᵐ[volume] (Ioc 0 (t : ℝ)).indicator (fun s => maLag n w rate ((t:ℝ)-s)) := by
 have hc (i : Fin n) : w i • SPDEExponentialForcing.responseVector (rate i) t =ᵐ[volume]
     fun s => w i * SPDEExponentialForcing.response (rate i) t s := by
   filter_upwards [Lp.coeFn_smul (w i) (SPDEExponentialForcing.responseVector (rate i) t),
     SPDEExponentialForcing.responseVector_coeFn (rate i) t] with s h1 h2
   change (w i • SPDEExponentialForcing.responseVector (rate i) t) s = _
   rw [h1]
   change w i * SPDEExponentialForcing.responseVector (rate i) t s = _
   rw [h2]
 filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => w i • SPDEExponentialForcing.responseVector (rate i) t),
   ae_all_iff.mpr hc] with s hs hc
 change (∑ i, w i • SPDEExponentialForcing.responseVector (rate i) t) s = _
 rw [hs]
 simp only [Finset.sum_apply]
 have he : (∑ i, (w i • SPDEExponentialForcing.responseVector (rate i) t) s) =
     ∑ i, w i * SPDEExponentialForcing.response (rate i) t s :=
   Finset.sum_congr rfl (fun i _ => hc i)
 rw [he]
 by_cases hst : s ∈ Ioc 0 (t : ℝ) <;> simp [maLag,SPDEExponentialForcing.response,hst]

theorem targetVector_coeFn (H : ℝ) (hH : 0<H) (t : ℝ≥0) :
 targetVector H hH t =ᵐ[volume] (Ioc 0 (t : ℝ)).indicator (fun s => targetLag H ((t:ℝ)-s)) := by
 filter_upwards [FractionalForcingKernel.responseVector_coeFn (H+1/2) (by linarith) t] with s hs
 change FractionalForcingKernel.responseVector (H+1/2) (by linarith) t s = _
 rw [hs]
 simp only [FractionalForcingKernel.response,GaussianPowerVolterra.kernel]
 rw [show H+1/2-1 = H-1/2 by ring]
 by_cases hst : s ∈ Ioc 0 (t : ℝ) <;> simp [targetLag,hst]

theorem errorVector_coeFn (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t : ℝ≥0) :
 errorVector n w rate H hH t =ᵐ[volume]
   (Ioc 0 (t : ℝ)).indicator (fun s => lagError n w rate H ((t:ℝ)-s)) := by
 filter_upwards [Lp.coeFn_sub (maVector n w rate t) (targetVector H hH t),
   maVector_coeFn n w rate t,targetVector_coeFn H hH t] with s hs hm ht
 change (maVector n w rate t-targetVector H hH t) s = _
 rw [hs]
 change maVector n w rate t s-targetVector H hH t s = _
 rw [hm,ht]
 by_cases hst : s ∈ Ioc 0 (t : ℝ) <;> simp [lagError,hst]

theorem error_square_coeFn (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t : ℝ≥0) :
 (fun s => errorVector n w rate H hH t s ^2) =ᵐ[volume]
   (Ioc 0 (t : ℝ)).indicator (fun s => lagError n w rate H ((t:ℝ)-s)^2) := by
 filter_upwards [errorVector_coeFn n w rate H hH t] with s hs
 rw [hs]
 by_cases hst : s ∈ Ioc 0 (t : ℝ) <;> simp [hst]

theorem lag_square_integrable (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t : ℝ≥0) :
 IntervalIntegrable (fun s => lagError n w rate H s ^2) volume 0 t := by
 have hi := (Lp.memLp (errorVector n w rate H hH t)).integrable_sq
 have hj := hi.congr (error_square_coeFn n w rate H hH t)
 rw [integrable_indicator_iff measurableSet_Ioc] at hj
 have hk := (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr hj
 have hc := hk.comp_sub_left (t : ℝ)
 simpa only [sub_sub_cancel,sub_self,sub_zero] using hc.symm

theorem error_energy (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t : ℝ≥0) :
 ‖errorObservable n w rate H hH t‖^2 = ∫ s in (0:ℝ)..(t:ℝ), lagError n w rate H s ^2 := by
 rw [errorObservable,LinearIsometry.norm_map,← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
 have he : (fun s => inner ℝ (errorVector n w rate H hH t s) (errorVector n w rate H hH t s)) =ᵐ[volume]
     (Ioc 0 (t : ℝ)).indicator (fun s => lagError n w rate H ((t:ℝ)-s)^2) := by
   simpa only [Real.inner_apply,pow_two] using error_square_coeFn n w rate H hH t
 rw [integral_congr_ae he,integral_indicator measurableSet_Ioc,
   ← intervalIntegral.integral_of_le t.coe_nonneg,
   intervalIntegral.integral_comp_sub_left (fun s => lagError n w rate H s ^2) (t:ℝ)]
 simp only [sub_self,sub_zero]

theorem error_energy_monotone (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) : Monotone (fun t : ℝ≥0 => ‖errorObservable n w rate H hH t‖^2) := by
 intro s t hst
 change ‖errorObservable n w rate H hH s‖^2 ≤ ‖errorObservable n w rate H hH t‖^2
 rw [error_energy,error_energy]
 exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg hst
   (Filter.Eventually.of_forall fun x => sq_nonneg _) (lag_square_integrable n w rate H hH t)

theorem time_error_integrable (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (a b : ℝ) :
 IntervalIntegrable (fun s : ℝ => ‖errorObservable n w rate H hH s.toNNReal‖^2) volume a b := by
 have hm : Monotone (fun s : ℝ => ‖errorObservable n w rate H hH s.toNNReal‖^2) := by
   intro s t hst
   exact error_energy_monotone n w rate H hH (Real.toNNReal_le_toNNReal hst)
 exact hm.intervalIntegrable

theorem averaged_endpoint_bound (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t S : ℝ≥0) (ht : t≤S) :
 ((S:ℝ)-t)*‖errorObservable n w rate H hH t‖^2 ≤
   ∫ s in (0:ℝ)..(S:ℝ), ‖errorObservable n w rate H hH s.toNNReal‖^2 := by
 have hi := intervalIntegral.integral_mono_on (show (t:ℝ)≤S from ht)
   (intervalIntegrable_const : IntervalIntegrable
     (fun _ : ℝ => ‖errorObservable n w rate H hH t‖^2) volume (t:ℝ) S)
   (time_error_integrable n w rate H hH t S) (fun s hs => by
     apply error_energy_monotone n w rate H hH
     change (t:ℝ)≤(s.toNNReal:ℝ)
     rw [Real.coe_toNNReal s (t.coe_nonneg.trans hs.1)]
     exact hs.1)
 simp only [intervalIntegral.integral_const,smul_eq_mul] at hi
 have hj := intervalIntegral.integral_mono_interval (a := (t:ℝ)) (b := (S:ℝ))
   (c := (0:ℝ)) (d := (S:ℝ)) t.coe_nonneg (show (t:ℝ)≤S from ht) le_rfl
   (Filter.Eventually.of_forall (fun s : ℝ => sq_nonneg ‖errorObservable n w rate H hH s.toNNReal‖))
   (time_error_integrable n w rate H hH 0 S)
 exact hi.trans hj

theorem interior_endpoint_bound (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t S : ℝ≥0) (ht : t<S) :
 ‖errorObservable n w rate H hH t‖^2 ≤
   (∫ s in (0:ℝ)..(S:ℝ), ‖errorObservable n w rate H hH s.toNNReal‖^2)/((S:ℝ)-t) := by
 apply (le_div_iff₀ (sub_pos.mpr (show (t:ℝ)<S from ht))).mpr
 simpa only [mul_comm] using averaged_endpoint_bound n w rate H hH t S ht.le

theorem uniform_interior_endpoint_bound (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t t0 S : ℝ≥0) (htt : t≤t0) (ht : t0<S) :
 ‖errorObservable n w rate H hH t‖^2 ≤
   (∫ s in (0:ℝ)..(S:ℝ), ‖errorObservable n w rate H hH s.toNNReal‖^2)/((S:ℝ)-t0) :=
 (error_energy_monotone n w rate H hH htt).trans (interior_endpoint_bound n w rate H hH t0 S ht)

theorem actual_interior_convergence (N : ℕ → ℕ) (w : (m : ℕ) → Fin (N m) → ℝ)
 (rate : (m : ℕ) → Fin (N m) → ℝ≥0) (H : ℝ) (hH : 0<H) (t S : ℝ≥0) (ht : t<S)
 (havg : Tendsto (fun m => ∫ s in (0:ℝ)..(S:ℝ),
   ‖errorObservable (N m) (w m) (rate m) H hH s.toNNReal‖^2) atTop (nhds 0)) :
 Tendsto (fun m => errorObservable (N m) (w m) (rate m) H hH t) atTop (nhds 0) := by
 have hs : Tendsto (fun m => ‖errorObservable (N m) (w m) (rate m) H hH t‖^2) atTop (nhds 0) := by
   apply squeeze_zero (fun m => sq_nonneg _) (fun m => interior_endpoint_bound (N m) (w m) (rate m) H hH t S ht)
   simpa only [zero_div] using havg.div_const ((S:ℝ)-t)
 have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
 apply tendsto_iff_norm_sub_tendsto_zero.mpr
 simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero,sub_zero] using hn

/-- Actual weighted Gaussian noising converges strictly inside the optimization
horizon, on the stated Bochner domains. No reverse-SDE convergence is inferred. -/
theorem weighted_actual_interior_convergence (N : ℕ → ℕ)
 (w : (m : ℕ) → Fin (N m) → ℝ) (rate : (m : ℕ) → Fin (N m) → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t S : ℝ≥0) (ht : t<S) (f q : ℝ → ℝ)
 (hk : ∀ m, IntervalIntegrable (fun s : ℝ => q s • maVector (N m) (w m) (rate m) s.toNNReal) volume 0 t)
 (hl : IntervalIntegrable (fun s : ℝ => q s • targetVector H hH s.toNNReal) volume 0 t)
 (M : ℝ) (hM : 0≤M) (hq : ∀ s ∈ Icc 0 (t:ℝ), |q s|≤M)
 (havg : Tendsto (fun m => ∫ s in (0:ℝ)..(S:ℝ),
   ‖errorObservable (N m) (w m) (rate m) H hH s.toNNReal‖^2) atTop (nhds 0)) :
 Tendsto (fun m => FractionalNoisingTransfer.weightedObservable
   (fun s : ℝ => maVector (N m) (w m) (rate m) s.toNNReal) f q t) atTop
   (nhds (FractionalNoisingTransfer.weightedObservable
     (fun s : ℝ => targetVector H hH s.toNNReal) f q t)) := by
 apply FractionalNoisingTransfer.weighted_convergence _ _ f q t hk hl M hM
   (fun m => ‖errorObservable (N m) (w m) (rate m) H hH t‖) (fun m => norm_nonneg _)
 · intro m s hs
   have hst : s.toNNReal≤t := by
     change (s.toNNReal:ℝ)≤t
     rw [Real.coe_toNNReal s hs.1]
     exact hs.2
   have hm := error_energy_monotone (N m) (w m) (rate m) H hH hst
   change ‖maVector (N m) (w m) (rate m) s.toNNReal-targetVector H hH s.toNNReal‖ ≤ _
   change ‖errorVector (N m) (w m) (rate m) H hH s.toNNReal‖ ≤ _
   rw [show ‖errorVector (N m) (w m) (rate m) H hH s.toNNReal‖ =
     ‖errorObservable (N m) (w m) (rate m) H hH s.toNNReal‖ by
       rw [errorObservable,LinearIsometry.norm_map]]
   nlinarith [norm_nonneg (errorObservable (N m) (w m) (rate m) H hH t),
     norm_nonneg (errorObservable (N m) (w m) (rate m) H hH s.toNNReal)]
 · exact hq
 · simpa only [norm_zero] using (actual_interior_convergence N w rate H hH t S ht havg).norm

theorem error_centered (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t : ℝ≥0) : ∫ ω, errorObservable n w rate H hH t ω ∂gaussianProduct = 0 :=
 GaussianHilbertProcess.isonormal_integral _

theorem error_native_input (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t : ℝ≥0) :
 GaussianTimeProductL2.productTensor (errorVector n w rate H hH t) gaussianOne ∈
   GaussianPredictableFull.fullPredictable := by
 apply GaussianDeterministicVolterra.positive_profile_predictable
 filter_upwards [errorVector_coeFn n w rate H hH t] with s hs hnon
 rw [hs]
 exact indicator_of_notMem (fun h => (not_lt.mpr hnon) h.1) _

theorem error_native_integral (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t : ℝ≥0) :
 GaussianPredictableFull.itoIntegral
   ⟨GaussianTimeProductL2.productTensor (errorVector n w rate H hH t) gaussianOne,
     error_native_input n w rate H hH t⟩ = errorObservable n w rate H hH t :=
 GaussianDeterministicIntegral.itoIntegral_deterministic _ _

theorem error_source_derivative (n : ℕ) (w : Fin n → ℝ) (rate : Fin n → ℝ≥0)
 (H : ℝ) (hH : 0<H) (t : ℝ≥0) :
 (errorObservable n w rate H hH t,GaussianContinuousRigidity.fieldEmbedding
   (GaussianTimeProductL2.productTensor (errorVector n w rate H hH t) gaussianOne)) ∈
     closedCylindricalDerivative.graph :=
 GaussianDeterministicIntegral.firstChaos_closedDerivative_graph _

end OperatorDerivativeRewrite.Foundation.FractionalMAHorizon
