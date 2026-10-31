import Foundation.PeriodicFullHaarGaussianLimit
import Foundation.PeriodicSlabL2
/-! Actual vacuum-versus-stationary normalization obstruction for the periodic
Wilson transfer. Vacuum-normalized Haar rows and every bounded core vanish;
every actual principal/vacuum ratio tends to zero. The constructed stationary
diagonal density diverges, while Markov row masses remain1. Exact bounded-core
ground conjugacy identifies the native L2 extension, whose norms tend to zero
under vacuum normalization. These are normalization facts, not gap closure. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicVacuumNormalizationObstruction
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
open PeriodicFullHaarGaussianLimit
open CubeHaarUpper (laplace laplace_pos)
attribute [local irreducible] kernel boundaryHaar GroundData.density

def vacuum (t : ℝ) : ℝ := kernel (1/t^2) (1 : State) 1

theorem vacuum_pos (t : ℝ) : 0<vacuum t := kernel_positive _ _ _

def rowBound (t : ℝ) : ℝ := laplace (1/t^2)^192/vacuum t

def powerBound (t : ℝ) : ℝ := PeriodicGroundHaarScale.upperConstant*|t|^387/(vacuum t/|t|^189)

theorem rowBound_nonneg (t : ℝ) : 0≤rowBound t := by
  unfold rowBound
  exact div_nonneg (pow_nonneg (laplace_pos (1/t^2) (by positivity)).le _) (vacuum_pos t).le

theorem laplace_scaled_power (t : ℝ) (ht : t≠0) (hsmall : |t|≤1) :
    laplace (1/t^2)^192 ≤ PeriodicGroundHaarScale.upperConstant*|t|^576 := by
  have hu := SU2HaarLaplaceUpper.laplace_scaled_upper 1 |t| (by norm_num) (abs_pos.mpr ht) hsmall
  rw [sq_abs] at hu
  have h := pow_le_pow_left₀ (laplace_pos (1/t^2) (by positivity)).le hu 192
  rw [mul_pow] at h
  simpa only [PeriodicGroundHaarScale.upperConstant,← pow_mul,show (3 : ℕ)*192=576 by decide] using h

theorem powerBound_tendsto : Tendsto powerBound (𝓝[≠] 0) (𝓝 0) := by
  have hc : Continuous (fun t : ℝ => PeriodicGroundHaarScale.upperConstant*|t|^387) :=
    continuous_const.mul (continuous_abs.pow 387)
  have hn : Tendsto (fun t : ℝ => PeriodicGroundHaarScale.upperConstant*|t|^387) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero,zero_pow (by decide : 387≠0),mul_zero] using
      hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ)≤𝓝 0)
  have hd := vacuum_kernel_limit
  have h := hn.div hd leadingConstant_pos.ne'
  unfold powerBound vacuum
  simp only [zero_div] at h
  convert h using 1

theorem rowBound_le_powerBound (t : ℝ) (ht : t≠0) (hsmall : |t|≤1) : rowBound t≤powerBound t := by
  have h := div_le_div_of_nonneg_right (laplace_scaled_power t ht hsmall) (vacuum_pos t).le
  have he : PeriodicGroundHaarScale.upperConstant*|t|^576/vacuum t=powerBound t := by
    unfold powerBound
    have hn := (vacuum_pos t).ne'
    have ha : |t|≠0 := abs_ne_zero.mpr ht
    field_simp
  exact h.trans_eq he

theorem rowBound_tendsto : Tendsto rowBound (𝓝[≠] 0) (𝓝 0) := by
  have hs : ∀ᶠ t : ℝ in 𝓝[≠] 0,|t|≤1 := by
    have hc : Continuous (fun t : ℝ => |t|) := continuous_abs
    exact ((hc.tendsto 0).eventually (Iio_mem_nhds (by norm_num : |(0 : ℝ)|<1))).mono
      (fun t ht => ht.le) |>.filter_mono nhdsWithin_le_nhds
  apply squeeze_zero' (Filter.Eventually.of_forall rowBound_nonneg) ?_ powerBound_tendsto
  filter_upwards [self_mem_nhdsWithin,hs] with t ht hsmall
  exact rowBound_le_powerBound t ht hsmall

def vacuumRow (t : ℝ) (U : State) : ℝ := (∫ V,kernel (1/t^2) U V ∂boundaryHaar)/vacuum t

theorem vacuumRow_nonneg (t : ℝ) (U : State) : 0≤vacuumRow t U :=
  div_nonneg (integral_nonneg (fun V => (kernel_positive _ _ _).le)) (vacuum_pos t).le

theorem vacuumRow_bound (t : ℝ) (U : State) : vacuumRow t U≤rowBound t :=
  div_le_div_of_nonneg_right (PeriodicGroundHaarScale.kernel_row_upper (1/t^2) (by positivity) U) (vacuum_pos t).le

theorem vacuumRow_tendsto (U : ℝ → State) :
    Tendsto (fun t : ℝ => vacuumRow t (U t)) (𝓝[≠] 0) (𝓝 0) :=
  squeeze_zero' (Filter.Eventually.of_forall (fun t => vacuumRow_nonneg t (U t)))
    (Filter.Eventually.of_forall (fun t => vacuumRow_bound t (U t))) rowBound_tendsto

theorem principal_ratio_bound (t : ℝ) (g : GroundData (1/t^2)) : g.value/vacuum t≤rowBound t :=
  div_le_div_of_nonneg_right
    (PeriodicGroundHaarScale.eigenvalue_laplace_upper (1/t^2) (by positivity) g) (vacuum_pos t).le

theorem principal_ratio_tendsto (g : (t : ℝ) → GroundData (1/t^2)) :
    Tendsto (fun t : ℝ => (g t).value/vacuum t) (𝓝[≠] 0) (𝓝 0) :=
  squeeze_zero' (Filter.Eventually.of_forall (fun t => div_nonneg (g t).value_pos.le (vacuum_pos t).le))
    (Filter.Eventually.of_forall (fun t => principal_ratio_bound t (g t))) rowBound_tendsto

theorem diagonal_density (t : ℝ) (g : GroundData (1/t^2)) :
    g.density (1 : State) 1=vacuum t/g.value := by
  unfold GroundData.density vacuum
  field_simp [(g.function_pos (1 : State)).ne',g.value_pos.ne']

theorem stationary_diagonal_tendsto (g : (t : ℝ) → GroundData (1/t^2)) :
    Tendsto (fun t : ℝ => (g t).density (1 : State) 1) (𝓝[≠] 0) atTop := by
  have hg : Tendsto (fun t : ℝ => (g t).value/vacuum t) (𝓝[≠] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨principal_ratio_tendsto g,Filter.Eventually.of_forall (fun t => div_pos (g t).value_pos (vacuum_pos t))⟩
  have h := tendsto_inv_nhdsGT_zero.comp hg
  simpa only [Function.comp_def,inv_div,diagonal_density] using h

theorem row_normalization_error (g : (t : ℝ) → GroundData (1/t^2)) (U : ℝ → State) :
    Tendsto (fun t : ℝ => |vacuumRow t (U t)-(∫ V,(g t).density (U t) V ∂boundaryHaar)|)
      (𝓝[≠] 0) (𝓝 1) := by
  simp only [GroundData.density_integral]
  have h := ((vacuumRow_tendsto U).sub_const 1).abs
  simpa only [zero_sub,abs_neg,abs_one] using h

def vacuumCore (t : ℝ) (f : State → ℝ) (U : State) : ℝ :=
  (∫ V,kernel (1/t^2) U V*f V ∂boundaryHaar)/vacuum t

theorem kernel_row_integrable (β : ℝ) (U : State) : Integrable (kernel β U) boundaryHaar := by
  have hm : Measurable (kernel β U) := (kernel_joint_measurable β).comp
    ((measurable_const : Measurable (fun _ : State => U)).prodMk measurable_id)
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (768*|β|))
  filter_upwards with V
  rw [Real.norm_eq_abs,abs_of_pos (kernel_positive _ _ _)]
  exact (kernel_bounds β U V).2

theorem core_integrable (β : ℝ) (U : State) (f : State → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ V,|f V|≤M) : Integrable (fun V => kernel β U V*f V) boundaryHaar := by
  have hm : Measurable (kernel β U) := (kernel_joint_measurable β).comp
    ((measurable_const : Measurable (fun _ : State => U)).prodMk measurable_id)
  apply Integrable.of_bound (hm.mul hf).aestronglyMeasurable (Real.exp (768*|β|)*M)
  filter_upwards with V
  change ‖kernel β U V*f V‖≤Real.exp (768*|β|)*M
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (kernel_positive _ _ _)]
  exact mul_le_mul (kernel_bounds β U V).2 (hb V) (abs_nonneg _) (Real.exp_pos _).le

theorem vacuumCore_bound (t : ℝ) (f : State → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0≤M)
    (hb : ∀ V,|f V|≤M) (U : State) : |vacuumCore t f U|≤M*rowBound t := by
  have hk := kernel_row_integrable (1/t^2) U
  have hi := core_integrable (1/t^2) U f hf M hb
  have h : ‖∫ V,kernel (1/t^2) U V*f V ∂boundaryHaar‖≤M*(∫ V,kernel (1/t^2) U V ∂boundaryHaar) := by
    calc
      _ ≤ ∫ V,‖kernel (1/t^2) U V*f V‖ ∂boundaryHaar := norm_integral_le_integral_norm _
      _ ≤ ∫ V,M*kernel (1/t^2) U V ∂boundaryHaar := by
        apply integral_mono hi.norm (hk.const_mul M)
        intro V
        change ‖kernel (1/t^2) U V*f V‖≤M*kernel (1/t^2) U V
        rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (kernel_positive _ _ _)]
        nlinarith [hb V,(kernel_positive (1/t^2) U V).le]
      _ = _ := integral_const_mul _ _
  unfold vacuumCore
  rw [abs_div,abs_of_pos (vacuum_pos t)]
  have hd := div_le_div_of_nonneg_right h (vacuum_pos t).le
  have hr := mul_le_mul_of_nonneg_left (vacuumRow_bound t U) hM
  have hd' : |∫ V,kernel (1/t^2) U V*f V ∂boundaryHaar|/vacuum t≤M*vacuumRow t U := by
    simpa only [Real.norm_eq_abs,mul_div_assoc,vacuumRow] using hd
  exact hd'.trans hr

theorem bounded_core_tendsto (f : ℝ → State → ℝ) (hf : ∀ t,Measurable (f t))
    (M : ℝ) (hM : 0≤M) (hb : ∀ t V,|f t V|≤M) (U : ℝ → State) :
    Tendsto (fun t : ℝ => vacuumCore t (f t) (U t)) (𝓝[≠] 0) (𝓝 0) := by
  apply squeeze_zero_norm' (Filter.Eventually.of_forall (fun t => ?_))
    (by simpa only [mul_zero] using rowBound_tendsto.const_mul M)
  simpa only [Real.norm_eq_abs] using vacuumCore_bound t (f t) (hf t) M hM (hb t) (U t)

def groundVacuumCore (t : ℝ) (g : GroundData (1/t^2)) (f : State → ℝ) (U : State) : ℝ :=
  vacuumCore t (fun V => g.function V*f V) U/g.function U

theorem ground_weighted_core_integrable (t : ℝ) (g : GroundData (1/t^2)) (f : State → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ V,|f V|≤M) (U : State) :
    Integrable (fun V => kernel (1/t^2) U V*(g.function V*f V)) boundaryHaar := by
  apply core_integrable (1/t^2) U (fun V => g.function V*f V) (g.measurable.mul hf) (|g.upper| *M)
  intro V
  rw [abs_mul]
  exact mul_le_mul ((g.bounds V).2.trans (le_abs_self _)) (hb V) (abs_nonneg _) (abs_nonneg _)

theorem groundVacuumCore_eq_transfer (t : ℝ) (g : GroundData (1/t^2)) (f : State → ℝ) (U : State) :
    groundVacuumCore t g f U=(g.value/vacuum t)*PeriodicSlabL2.transfer g f U := by
  unfold groundVacuumCore vacuumCore PeriodicSlabL2.transfer
  rw [g.transition_integral]
  field_simp [(vacuum_pos t).ne',g.value_pos.ne',(g.function_pos U).ne']

theorem groundVacuumCore_memLp (t : ℝ) (g : GroundData (1/t^2)) (f : State → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ U,|f U|≤M) :
    MemLp (groundVacuumCore t g f) 2 g.stationary := by
  have he : groundVacuumCore t g f=(g.value/vacuum t) • PeriodicSlabL2.transfer g f := by
    funext U
    exact groundVacuumCore_eq_transfer t g f U
  rw [he]
  exact (PeriodicSlabL2.transfer_memLp g f hf M hb).const_smul _

/-- The actual Haar vacuum normalization, after conjugating by the actual
ground function, agrees on the bounded core with this scalar multiple of the
verified native stationary L2 operator. -/
def conjugateVacuumOperator (t : ℝ) (g : GroundData (1/t^2)) :
    PeriodicSlabL2.StateL2 g →L[ℝ] PeriodicSlabL2.StateL2 g :=
  (g.value/vacuum t) • PeriodicSlabL2.operator g

theorem conjugateVacuumOperator_toLp (t : ℝ) (g : GroundData (1/t^2)) (f : State → ℝ)
    (hm : MemLp f 2 g.stationary) (hf : Measurable f) (M : ℝ) (hb : ∀ U,|f U|≤M) :
    conjugateVacuumOperator t g (hm.toLp f)=
      (groundVacuumCore_memLp t g f hf M hb).toLp (groundVacuumCore t g f) := by
  unfold conjugateVacuumOperator
  rw [ContinuousLinearMap.smul_apply,PeriodicSlabL2.operator_toLp g f hm hf M hb]
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (g.value/vacuum t)
      ((PeriodicSlabL2.transfer_memLp g f hf M hb).toLp (PeriodicSlabL2.transfer g f)),
    MemLp.coeFn_toLp (PeriodicSlabL2.transfer_memLp g f hf M hb),
    MemLp.coeFn_toLp (groundVacuumCore_memLp t g f hf M hb)] with U hs hp hq
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hp,hq]
  exact (groundVacuumCore_eq_transfer t g f U).symm

theorem native_operator_norm_le (β : ℝ) (g : GroundData β) : ‖PeriodicSlabL2.operator g‖≤1 :=
  (PeriodicSlabL2.operator g).opNorm_le_bound (by norm_num) (fun F => by
    simpa only [one_mul] using PeriodicSlabL2.operator_contraction g F)

theorem conjugateVacuumOperator_norm_bound (t : ℝ) (g : GroundData (1/t^2)) :
    ‖conjugateVacuumOperator t g‖≤g.value/vacuum t := by
  unfold conjugateVacuumOperator
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos g.value_pos (vacuum_pos t))]
  exact (mul_le_mul_of_nonneg_left (native_operator_norm_le _ g)
    (div_pos g.value_pos (vacuum_pos t)).le).trans_eq (mul_one _)

theorem conjugateVacuumOperator_norm_tendsto (g : (t : ℝ) → GroundData (1/t^2)) :
    Tendsto (fun t : ℝ => ‖conjugateVacuumOperator t (g t)‖) (𝓝[≠] 0) (𝓝 0) :=
  squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (Filter.Eventually.of_forall (fun t => conjugateVacuumOperator_norm_bound t (g t)))
    (principal_ratio_tendsto g)

end OperatorDerivativeRewrite.Foundation.PeriodicVacuumNormalizationObstruction
