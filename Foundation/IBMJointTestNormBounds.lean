import Foundation.IBMJointBanachTestSpace

/-! Explicit bounds in the stronger completed test norm. The bound comes from
actual endpoint and squared-increment moments, not from Hilbert norm control
of the original native integral. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMJointTestNormBounds
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMJointCompletedTestGraph IBMJointBanachTestSpace IBMSpatialRandomTestBounds

theorem endpointWeight_eq_single_variation (T : ℝ≥0) :
    IBMSpatialSignedRandomTests.endpointWeight T = quadraticVariation (uniformTime T 0) := by
  apply Lp.ext
  filter_upwards [(IBMSpatialSignedRandomTests.clock_square_memLp T).coeFn_toLp,
    quadraticVariation_coeFn (uniformTime T 0) (uniformTime_monotone T 0),
    process_zero_ae,IBMConstructedSources.clockPath_coordinate_ae T] with Y he hq hz hc
  change IBMSpatialSignedRandomTests.endpointWeight T Y = _ at he
  rw [he,hc]
  simpa [uniformTime,hz] using hq.symm

theorem endpointWeight_norm_bound (T : ℝ≥0) :
    ‖IBMSpatialSignedRandomTests.endpointWeight T‖ ≤ 3*(T:ℝ) := by
  rw [endpointWeight_eq_single_variation]
  exact quadraticVariation_norm_bound T 0

theorem signed_random_bound (T : ℝ≥0) (N : ℕ) (u : RandomTests) :
    ‖IBMSpatialSignedRandomTests.finiteOperator T N u‖ ≤ 6*(T:ℝ)*‖u‖ := by
  have he := IBMWeakRandomEvaluation.value_bound
    (IBMSpatialSignedRandomTests.endpointPath T) (IBMSpatialSignedRandomTests.endpointPath_measurable T)
    (IBMSpatialSignedRandomTests.endpointWeight T) (IBMSpatialSignedRandomTests.endpointPath_bound T) u
  have hn := mul_le_mul_of_nonneg_right (endpointWeight_norm_bound T) (norm_nonneg u)
  have hf := finite_norm_bound T N u
  have hs := norm_sub_le (IBMSpatialSignedRandomTests.endpointOperator T u)
    (IBMSpatialRandomTestBounds.finiteOperator T N u)
  change ‖IBMSpatialSignedRandomTests.endpointOperator T u‖ ≤ _ at he
  change ‖IBMSpatialSignedRandomTests.endpointOperator T u-
    IBMSpatialRandomTestBounds.finiteOperator T N u‖ ≤ _
  linarith

theorem graph_symbol_bound (p : Graph) : ‖symbolMap p‖ ≤ ‖p‖ := by
  change ‖(p:IBMTimeAveragedObservable.JointL2 × RandomTests).2‖ ≤
    ‖(p:IBMTimeAveragedObservable.JointL2 × RandomTests)‖
  exact norm_snd_le _

theorem graph_native_bound (T : ℝ≥0) (N : ℕ) (p : Graph) :
    ‖finiteFunctional T N p‖ ≤ 6*(T:ℝ)*‖p‖ := by
  change ‖inner ℝ (IBMTimeAveragedObservable.jointRealization
    (IBMRawGridSecondChaos.sourceGrid (T/(N+1)) (N+1))) (jointMap p)‖ ≤ _
  rw [finite_identity]
  have hi := L1.norm_integral_le (IBMSpatialSignedRandomTests.finiteOperator T N (symbolMap p))
  rw [L1.integral_eq] at hi
  exact (hi.trans (signed_random_bound T N (symbolMap p))).trans
    (mul_le_mul_of_nonneg_left (graph_symbol_bound p) (by positivity))

theorem realization_norm_le (x : Tests) : ‖realize x‖ ≤ ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨p,hp,hpn⟩ := Submodule.Quotient.norm_mk_lt x hε
  have he : realize x = jointMap p := by rw [← hp]; rfl
  rw [he]
  have hj : ‖jointMap p‖ ≤ ‖p‖ := by
    change ‖(p:IBMTimeAveragedObservable.JointL2 × RandomTests).1‖ ≤
      ‖(p:IBMTimeAveragedObservable.JointL2 × RandomTests)‖
    exact norm_fst_le _
  exact (hj.trans_lt hpn).le

theorem native_bound (T : ℝ≥0) (N : ℕ) (x : Tests) :
    ‖nativeFunctional T N x‖ ≤ 6*(T:ℝ)*‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hd : 0 < ε/(6*(T:ℝ)+1) := by positivity
  obtain ⟨p,hp,hpn⟩ := Submodule.Quotient.norm_mk_lt x hd
  have he : nativeFunctional T N x = finiteFunctional T N p := by rw [← hp]; rfl
  rw [he]
  have hb := graph_native_bound T N p
  have hs : 6*(T:ℝ)*(ε/(6*(T:ℝ)+1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 6*(T:ℝ)+1 by positivity)).mpr
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hpn.le (show 0 ≤ 6*(T:ℝ) by positivity)
  nlinarith

theorem distribution_bound (T : ℝ≥0) (hT : 0 < T) (x : Tests) :
    ‖distribution T hT x‖ ≤ 6*(T:ℝ)*‖x‖ :=
  le_of_tendsto (native_tendsto T hT x).norm (Eventually.of_forall fun N => native_bound T N x)

end OperatorDerivativeRewrite.Foundation.IBMJointTestNormBounds
