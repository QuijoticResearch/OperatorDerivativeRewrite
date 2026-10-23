import Foundation.IBMTimeWeightedClockDensity

/-! Genuine full-field strong convergence for every deterministic L2 weight,
obtained from original prefix limits and the verified uniform energy bound. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTimeWeightedClockStrong
open InfiniteGaussian IBMClockOverlapEnergy IBMIntrinsicOperators IBMClockVectorTranspose
open IBMTimeWeightedClockOperator IBMTimeWeightedClockDensity IBMTimeWeightedSineClock
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem indicator_native (n : ℕ) (T : ℝ≥0) (s : Set ℝ) (hs : MeasurableSet s) :
    nativeOperator n T (indicatorConstLp 2 hs (measure_ne_top (window T) s) (1:ℝ)) =
      clockField (∫ t in s, IBMNonlinearClockField.field n t ∂window T) := by
  change nativeGradient n _ T = _
  have he : (indicatorConstLp 2 hs (measure_ne_top (window T) s) (1:ℝ) : ℝ → ℝ)
      =ᵐ[window T] s.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  rw [native_congr n _ _ T he]
  unfold nativeGradient
  congr 1
  have hi : (fun t => s.indicator (fun _ => (1:ℝ)) t • IBMNonlinearClockField.field n t) =
      s.indicator (IBMNonlinearClockField.field n) := by
    funext t
    by_cases ht : t ∈ s <;> simp [ht]
  rw [hi,integral_indicator hs]

theorem prefix_intersection (T : ℝ≥0) (a : ℝ) :
    Iic a ∩ Ioc 0 (T:ℝ) = Ioc 0 (((min a (T:ℝ)).toNNReal : ℝ≥0) : ℝ) := by
  by_cases ha : 0 ≤ min a (T:ℝ)
  · rw [Real.coe_toNNReal _ ha]
    ext t
    simp only [mem_inter_iff,mem_Iic,mem_Ioc,le_min_iff]
    tauto
  · have hh : min a (T:ℝ) ≤ 0 := le_of_not_ge ha
    rw [Real.toNNReal_of_nonpos hh]
    ext t
    simp only [mem_inter_iff,mem_Iic,mem_Ioc,NNReal.coe_zero]
    constructor
    · rintro ⟨hta,ht,htT⟩
      have hmin : t ≤ min a (T:ℝ) := le_min hta htT
      exact ⟨ht,by linarith⟩
    · rintro ⟨ht,ht0⟩
      linarith

theorem prefix_native (n : ℕ) (T : ℝ≥0) (a : ℝ) :
    nativeOperator n T
      (indicatorConstLp 2 measurableSet_Iic (measure_ne_top (window T) (Iic a)) (1:ℝ)) =
        IBMNonlinearClockAverageGraph.averageGradient n (min a (T:ℝ)).toNNReal := by
  rw [indicator_native]
  unfold window
  rw [Measure.restrict_restrict measurableSet_Iic,prefix_intersection]
  rfl

theorem prefix_converges (T : ℝ≥0) (a : ℝ) :
    indicatorConstLp 2 measurableSet_Iic (measure_ne_top (window T) (Iic a)) (1:ℝ)
      ∈ convergent T := by
  refine ⟨IBMSineAverageIntrinsicCalculus.gradient (min a (T:ℝ)).toNNReal 1,?_⟩
  simpa only [prefix_native] using
    IBMSineAverageStrongClock.clockGradient_tendsto (min a (T:ℝ)).toNNReal

theorem convergent_eq_top (T : ℝ≥0) : convergent T = ⊤ := by
  apply all_of_prefix T
  intro s hs hm
  rcases hs with rfl | ⟨a,rfl⟩
  · refine ⟨IBMSineAverageIntrinsicCalculus.gradient T 1,?_⟩
    simpa only [indicator_native,setIntegral_univ,
      IBMNonlinearClockAverageGraph.averageGradient,IBMNonlinearClockEnergy.average] using
      IBMSineAverageStrongClock.clockGradient_tendsto T
  · exact prefix_converges T a

attribute [local irreducible] IBMTimeWeightedSineCalculus.gradient
  IBMTimeWeightedSineCalculus.domainValue IBMTimeWeightedSineValue.actual

theorem native_tendsto (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    Tendsto (fun n => nativeGradient n g T) atTop
      (𝓝 (IBMTimeWeightedSineCalculus.gradient g T hg 1)) := by
  have hm : hg.toLp g ∈ convergent T := by rw [convergent_eq_top]; trivial
  obtain ⟨v,hv⟩ := hm
  have he (n : ℕ) : nativeOperator n T (hg.toLp g) = nativeGradient n g T :=
    native_congr n _ _ T (MemLp.coeFn_toLp hg)
  have ht : Tendsto (fun n => nativeGradient n g T) atTop (𝓝 v) := by
    simpa only [he] using hv
  have hactual : v = IBMTimeWeightedSineCalculus.gradient g T hg 1 := by
    apply ext_inner_right ℝ
    intro w
    exact tendsto_nhds_unique (ht.inner tendsto_const_nhds)
      (IBMTimeWeightedSineCalculus.native_clock_pairing_tendsto g T hg w)
  exact hactual ▸ ht

theorem native_error_tendsto (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    Tendsto (fun n => ‖nativeGradient n g T -
      IBMTimeWeightedSineCalculus.gradient g T hg 1‖) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp (native_tendsto g T hg)

theorem actual_clock_graph_tendsto (g : ℝ → ℝ) (T : ℝ≥0)
    (hg : MemLp g 2 (window T)) :
    Tendsto (fun n => (clockUnitary (IBMTimeWeightedSineValue.mollified n g T),
      nativeGradient n g T)) atTop
      (𝓝 (clockUnitary (IBMTimeWeightedSineValue.actual g T : IBMTimeAveragedObservable.JointL2),
        IBMTimeWeightedSineCalculus.gradient g T hg 1)) :=
  (clockUnitary.continuous.continuousAt.tendsto.comp
    (IBMTimeWeightedSineValue.mollified_tendsto g T hg)).prodMk_nhds (native_tendsto g T hg)

theorem moving_time_weights_tendsto (T : ℝ≥0) (u : ℕ → TimeL2 T) (g : TimeL2 T)
    (hu : Tendsto u atTop (𝓝 g)) :
    Tendsto (fun n => nativeOperator n T (u n)) atTop
      (𝓝 (IBMTimeWeightedSineCalculus.gradient g T (Lp.memLp g) 1)) := by
  have hd : Tendsto (fun n => dist (nativeOperator n T g) (nativeOperator n T (u n)))
      atTop (𝓝 0) := by
    have ht : Tendsto (fun n => bound T * dist g (u n)) atTop (𝓝 0) := by
      simpa only [dist_self,mul_zero] using
        ((tendsto_const_nhds (x := g)).dist hu).const_mul (bound T)
    exact squeeze_zero (fun n => dist_nonneg) (fun n => nativeOperator_difference n T g (u n)) ht
  exact (native_tendsto g T (Lp.memLp g)).congr_dist hd

end OperatorDerivativeRewrite.Foundation.IBMTimeWeightedClockStrong
