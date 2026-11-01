import Foundation.PeriodicTemporalParity
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
/-! Actual temporal Wilson Laplace integrals and quantitative Taylor control.
Reference-Haar moments are inserted only after proving the exponential remainder. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicTemporalLaplaceContrast
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab
open PeriodicTemporalParity
attribute [local irreducible] gaugeHaar kernel spatialAction temporalAction

theorem trace_measurable (U V : State) : Measurable (traceSum U V) := by
  unfold traceSum
  apply Finset.measurable_sum
  intro e _
  exact halfTrace_measurable.comp (by unfold temporalWord; fun_prop)

theorem trace_bound (U V : State) (a : Gauge) : |traceSum U V a| ≤ 192 := by
  unfold traceSum
  calc
    _ ≤ ∑ e : SpatialEdge, |halfTrace (temporalWord U V a e)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e : SpatialEdge, (1 : ℝ) := Finset.sum_le_sum (fun e _ => halfTrace_bound _)
    _ = 192 := by simp [edge_count]

def weighted (β : ℝ) (U V : State) (f : Gauge → ℝ) : ℝ :=
  ∫ a, f a*Real.exp (β*traceSum U V a) ∂gaugeHaar

def partition (β : ℝ) (U V : State) : ℝ := weighted β U V (fun _ => 1)

def polynomial (n : ℕ) (β x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (β*x)^k/(Nat.factorial k : ℝ)

def weightedPolynomial (n : ℕ) (β : ℝ) (U V : State) (f : Gauge → ℝ) : ℝ :=
  ∫ a, f a*polynomial n β (traceSum U V a) ∂gaugeHaar

def errorBound (n : ℕ) (β : ℝ) : ℝ := (192*|β|)^n*Real.exp (192*|β|)

private theorem real_exp_error (n : ℕ) (x : ℝ) :
    |Real.exp x-∑ k ∈ Finset.range n, x^k/(Nat.factorial k : ℝ)| ≤ |x|^n*Real.exp |x| := by
  have hh := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) n
  have he : ((Real.exp x-∑ k ∈ Finset.range n, x^k/(Nat.factorial k : ℝ) : ℝ) : ℂ) =
      Complex.exp (x : ℂ)-∑ k ∈ Finset.range n, (x : ℂ)^k/(Nat.factorial k : ℂ) := by
    simp
  rw [← he,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs] at hh
  exact hh

private theorem point_error (n : ℕ) (β : ℝ) (U V : State) (a : Gauge) :
    |Real.exp (β*traceSum U V a)-polynomial n β (traceSum U V a)| ≤ errorBound n β := by
  have hb : |β*traceSum U V a| ≤ 192*|β| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (trace_bound U V a) (abs_nonneg β)).trans_eq (by ring)
  apply (real_exp_error n (β*traceSum U V a)).trans
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hb n) (Real.exp_le_exp.mpr hb)
    (Real.exp_pos _).le (by positivity)

private theorem bounded_power_integrable (U V : State) (k : ℕ) :
    Integrable (fun a => (traceSum U V a)^k) gaugeHaar := by
  apply Integrable.of_bound ((trace_measurable U V).pow_const k).aestronglyMeasurable (192^k)
  filter_upwards with a
  simpa only [Real.norm_eq_abs,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (trace_bound U V a) k

private theorem exp_integrable (β : ℝ) (U V : State) :
    Integrable (fun a => Real.exp (β*traceSum U V a)) gaugeHaar := by
  apply Integrable.of_bound ((trace_measurable U V).const_mul β |>.exp).aestronglyMeasurable
    (Real.exp (192*|β|))
  filter_upwards with a
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    β*traceSum U V a ≤ |β*traceSum U V a| := le_abs_self _
    _ = |β| *|traceSum U V a| := abs_mul _ _
    _ ≤ |β| *192 := mul_le_mul_of_nonneg_left (trace_bound U V a) (abs_nonneg β)
    _ = 192*|β| := by ring

theorem weighted_taylor_bound (n : ℕ) (β : ℝ) (U V : State) (f : Gauge → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ a, |f a| ≤ M) :
    |weighted β U V f-weightedPolynomial n β U V f| ≤ M*errorBound n β := by
  let R := fun a : Gauge => f a*(Real.exp (β*traceSum U V a)-polynomial n β (traceSum U V a))
  have hi (a : Gauge) : |R a| ≤ M*errorBound n β := by
    change |f a*(Real.exp (β*traceSum U V a)-polynomial n β (traceSum U V a))| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hb a) (point_error n β U V a) (abs_nonneg _) hM
  have hm : Measurable R := by
    apply hf.mul
    apply Measurable.sub ((trace_measurable U V).const_mul β |>.exp)
    unfold polynomial
    apply Finset.measurable_sum
    intro k _
    exact (((trace_measurable U V).const_mul β).pow_const k).div_const _
  have hr : Integrable R gaugeHaar := Integrable.of_bound hm.aestronglyMeasurable
    (M*errorBound n β) (ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs] using hi a))
  have hw : Integrable (fun a => f a*Real.exp (β*traceSum U V a)) gaugeHaar := by
    apply Integrable.mono' ((exp_integrable β U V).const_mul M)
      (hf.mul ((trace_measurable U V).const_mul β |>.exp)).aestronglyMeasurable
    filter_upwards with a
    change ‖f a*Real.exp (β*traceSum U V a)‖ ≤ _
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hb a) (Real.exp_pos _).le
  have hp : Integrable (fun a => f a*polynomial n β (traceSum U V a)) gaugeHaar := by
    apply (hw.sub hr).congr
    filter_upwards with a
    change f a*Real.exp (β*traceSum U V a)-R a=f a*polynomial n β (traceSum U V a)
    dsimp only [R]
    ring
  have he : weighted β U V f-weightedPolynomial n β U V f = ∫ a, R a ∂gaugeHaar := by
    unfold weighted weightedPolynomial
    rw [← integral_sub hw hp]
    apply integral_congr_ae
    filter_upwards with a
    dsimp only [R]
    ring
  rw [he]
  have hh := norm_integral_le_of_norm_le_const (μ := gaugeHaar) (f := R)
    (C := M*errorBound n β) (ae_of_all _ (fun a =>
    (by simpa only [Real.norm_eq_abs] using hi a)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

def massPolynomial (n : ℕ) (β : ℝ) (U V : State) : ℝ :=
  ∑ k ∈ Finset.range n, β^k/(Nat.factorial k : ℝ)*powerMoment k U V

theorem polynomial_mass (n : ℕ) (β : ℝ) (U V : State) :
    weightedPolynomial n β U V (fun _ => 1)=massPolynomial n β U V := by
  unfold weightedPolynomial polynomial massPolynomial
  simp only [one_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [show (fun a => (β*traceSum U V a)^k/(Nat.factorial k : ℝ)) =
      (fun a => (β^k/(Nat.factorial k : ℝ))*(traceSum U V a)^k) by
        funext a; rw [mul_pow]; ring,integral_const_mul]
    rfl
  · intro k _
    have ht := (bounded_power_integrable U V k).const_mul (β^k/(Nat.factorial k : ℝ))
    convert ht using 1
    funext a
    rw [mul_pow]
    ring

theorem partition_taylor_bound (n : ℕ) (β : ℝ) (U V : State) :
    |partition β U V-massPolynomial n β U V| ≤ errorBound n β := by
  have ht := weighted_taylor_bound n β U V (fun _ => 1) measurable_const 1
    (by norm_num) (fun _ => by norm_num)
  rw [polynomial_mass,one_mul] at ht
  exact ht

theorem quartic_polynomial_contrast (β h : ℝ) :
    massPolynomial 5 β (PeriodicTemporalCycleMoment.orbit h) 1 -
      massPolynomial 5 β (PeriodicTemporalCycleMoment.orbit h) (PeriodicCenterSeam.flip 1 1) =
        β^4/2*Real.cos (4*h) := by
  let U := PeriodicTemporalCycleMoment.orbit h
  unfold massPolynomial
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  rw [Finset.sum_range_succ]
  have hz : (∑ k ∈ Finset.range 4, β^k/(Nat.factorial k : ℝ)*
      (powerMoment k U 1-powerMoment k U (PeriodicCenterSeam.flip 1 1)))=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [power_moment_twist_low_order (Finset.mem_range.mp hk),sub_self,mul_zero]
  rw [hz,full_quartic_orbit]
  norm_num [Nat.factorial]
  ring

theorem partition_contrast_bound (β h : ℝ) :
    |partition β (PeriodicTemporalCycleMoment.orbit h) 1-
      partition β (PeriodicTemporalCycleMoment.orbit h) (PeriodicCenterSeam.flip 1 1)-
        β^4/2*Real.cos (4*h)| ≤ 2*errorBound 5 β := by
  let U := PeriodicTemporalCycleMoment.orbit h
  let V := PeriodicCenterSeam.flip 1 (1 : State)
  have ha := partition_taylor_bound 5 β U 1
  have hb := partition_taylor_bound 5 β U V
  have he := quartic_polynomial_contrast β h
  change massPolynomial 5 β U 1-massPolynomial 5 β U V=_ at he
  change |partition β U 1-partition β U V-β^4/2*Real.cos (4*h)| ≤ _
  rw [← he]
  calc
    _ = |(partition β U 1-massPolynomial 5 β U 1)-
        (partition β U V-massPolynomial 5 β U V)| := by congr 1; ring
    _ ≤ |partition β U 1-massPolynomial 5 β U 1|+
        |partition β U V-massPolynomial 5 β U V| := abs_sub _ _
    _ ≤ 2*errorBound 5 β := by linarith

def prefactor (β : ℝ) (U V : State) : ℝ :=
  Real.exp (-β*(spatialAction U/2+spatialAction V/2+192))

theorem prefactor_pos (β : ℝ) (U V : State) : 0 < prefactor β U V := Real.exp_pos _

theorem temporal_trace_action (U V : State) (a : Gauge) :
    temporalAction U V a=192-traceSum U V a := by
  unfold temporalAction traceSum
  rw [Finset.sum_sub_distrib]
  simp [edge_count]

theorem weight_factor (β : ℝ) (U V : State) (a : Gauge) :
    weight β U V a=prefactor β U V*Real.exp (β*traceSum U V a) := by
  unfold weight halfAction prefactor
  rw [temporal_trace_action,← Real.exp_add]
  congr 1
  ring

theorem kernel_factor (β : ℝ) (U V : State) : kernel β U V=prefactor β U V*partition β U V := by
  unfold kernel
  simp_rw [weight_factor]
  rw [integral_const_mul]
  simp only [partition,weighted,one_mul]

theorem partition_pos (β : ℝ) (U V : State) : 0 < partition β U V := by
  have hh := kernel_positive β U V
  rw [kernel_factor] at hh
  exact (mul_pos_iff_of_pos_left (prefactor_pos β U V)).mp hh

theorem prefactor_twist (β : ℝ) (U V : State) :
    prefactor β U (PeriodicCenterSeam.flip 1 V)=prefactor β U V := by
  unfold prefactor
  rw [PeriodicCenterSeam.spatial_action]

theorem kernel_log_contrast (β : ℝ) (U V : State) :
    Real.log (kernel β U V)-Real.log (kernel β U (PeriodicCenterSeam.flip 1 V)) =
      Real.log (partition β U V)-Real.log (partition β U (PeriodicCenterSeam.flip 1 V)) := by
  rw [kernel_factor,kernel_factor,prefactor_twist,
    Real.log_mul (prefactor_pos β U V).ne' (partition_pos β U V).ne',
    Real.log_mul (prefactor_pos β U V).ne' (partition_pos β U (PeriodicCenterSeam.flip 1 V)).ne']
  ring

private theorem slot_trace (L R : SU2) (h : ℝ) :
    halfTrace (L*SU2JointPlaquetteCubic.axis 0 h*R)=Real.cos h*halfTrace (L*R)+
      Real.sin h*halfTrace (L*SU2JointPlaquetteCubic.axis 0 (Real.pi/2)*R) := by
  simp only [halfTrace,Submonoid.coe_mul,SU2AxisMatrixJets.axis_matrix_formula,
    Real.cos_pi_div_two,Real.sin_pi_div_two,zero_smul,one_smul,zero_add,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
    SU2TraceHessianModel.traceReal,Matrix.trace_add,Matrix.trace_smul,
    Complex.add_re,Complex.smul_re,smul_eq_mul]
  ring

theorem trace_rotation (U V : State) (a : Gauge) (h : ℝ) :
    traceSum (PeriodicEndpointScore.left h U) V a = Real.cos h*traceSum U V a+
      Real.sin h*traceSum (PeriodicEndpointScore.left (Real.pi/2) U) V a := by
  have he (e : SpatialEdge) :
      halfTrace (temporalWord (PeriodicEndpointScore.left h U) V a e) =
        Real.cos h*halfTrace (temporalWord U V a e)+
          Real.sin h*halfTrace (temporalWord (PeriodicEndpointScore.left (Real.pi/2) U) V a e) := by
    simpa only [temporalWord,PeriodicEndpointScore.left,one_mul,mul_assoc] using
      slot_trace 1 (U e*a (shift e.1 e.2)*(V e)⁻¹*(a e.1)⁻¹) h
  unfold traceSum
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]

def cTrace (h : ℝ) (U V : State) (a : Gauge) : ℝ :=
  traceSum (PeriodicEndpointScore.left h U) V a

def dTrace (h : ℝ) (U V : State) (a : Gauge) : ℝ :=
  -Real.sin h*traceSum U V a+
    Real.cos h*traceSum (PeriodicEndpointScore.left (Real.pi/2) U) V a

theorem dTrace_shift (h : ℝ) (U V : State) (a : Gauge) :
    dTrace h U V a=traceSum (PeriodicEndpointScore.left (h+Real.pi/2) U) V a := by
  rw [trace_rotation]
  simp [dTrace,Real.cos_add,Real.sin_add]

theorem cTrace_derivative (h : ℝ) (U V : State) (a : Gauge) :
    HasDerivAt (fun t => cTrace t U V a) (dTrace h U V a) h := by
  have hd := ((Real.hasDerivAt_cos h).mul_const (traceSum U V a)).add
    ((Real.hasDerivAt_sin h).mul_const (traceSum (PeriodicEndpointScore.left (Real.pi/2) U) V a))
  convert hd using 1
  · funext t
    exact trace_rotation U V a t
  · rfl

theorem dTrace_derivative (h : ℝ) (U V : State) (a : Gauge) :
    HasDerivAt (fun t => dTrace t U V a) (-cTrace h U V a) h := by
  have hd := (((Real.hasDerivAt_sin h).neg).mul_const (traceSum U V a)).add
    ((Real.hasDerivAt_cos h).mul_const (traceSum (PeriodicEndpointScore.left (Real.pi/2) U) V a))
  convert hd using 1
  · rfl
  · rw [cTrace,trace_rotation]
    ring

theorem cTrace_bound (h : ℝ) (U V : State) (a : Gauge) : |cTrace h U V a| ≤ 192 := trace_bound _ _ _
theorem dTrace_bound (h : ℝ) (U V : State) (a : Gauge) : |dTrace h U V a| ≤ 192 := by
  rw [dTrace_shift]
  exact trace_bound _ _ _

theorem cTrace_measurable (h : ℝ) (U V : State) : Measurable (cTrace h U V) := trace_measurable _ _
theorem dTrace_measurable (h : ℝ) (U V : State) : Measurable (dTrace h U V) := by
  exact ((trace_measurable U V).const_mul (-Real.sin h)).add
    ((trace_measurable _ V).const_mul (Real.cos h))

def firstJet (β : ℝ) (U V : State) (h : ℝ) : ℝ :=
  ∫ a, Real.exp (β*cTrace h U V a)*(β*dTrace h U V a) ∂gaugeHaar

def secondJet (β : ℝ) (U V : State) (h : ℝ) : ℝ :=
  ∫ a, Real.exp (β*cTrace h U V a)*((β*dTrace h U V a)^2-β*cTrace h U V a) ∂gaugeHaar

private theorem phase_bound (β h : ℝ) (U V : State) (a : Gauge) :
    |β*cTrace h U V a| ≤ 192*|β| := by
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (cTrace_bound h U V a) (abs_nonneg β)).trans_eq (by ring)

private theorem slope_bound (β h : ℝ) (U V : State) (a : Gauge) :
    |β*dTrace h U V a| ≤ 192*|β| := by
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (dTrace_bound h U V a) (abs_nonneg β)).trans_eq (by ring)

private theorem curvature_bound (β h : ℝ) (U V : State) (a : Gauge) :
    |(β*dTrace h U V a)^2-β*cTrace h U V a| ≤ (192*|β|)^2+192*|β| := by
  have hh := slope_bound β h U V a
  have hp : (β*dTrace h U V a)^2 ≤ (192*|β|)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hh
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg (sq_nonneg _)]
  linarith [phase_bound β h U V a]

theorem partition_derivative (β : ℝ) (U V : State) (t : ℝ) :
    HasDerivAt (fun h => partition β (PeriodicEndpointScore.left h U) V) (firstJet β U V t) t := by
  let F := fun h a => Real.exp (β*cTrace h U V a)
  let G := fun h a => Real.exp (β*cTrace h U V a)*(β*dTrace h U V a)
  let E := Real.exp (192*|β|)
  have he (h : ℝ) (a : Gauge) : Real.exp (β*cTrace h U V a) ≤ E :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (phase_bound β h U V a))
  have hm (h : ℝ) : AEStronglyMeasurable (F h) gaugeHaar :=
    ((cTrace_measurable h U V).const_mul β |>.exp).aestronglyMeasurable
  have hi : Integrable (F t) gaugeHaar := by
    apply Integrable.of_bound (hm t) E
    filter_upwards with a
    change ‖Real.exp (β*cTrace t U V a)‖ ≤ _
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using he t a
  have hg : AEStronglyMeasurable (G t) gaugeHaar :=
    (((cTrace_measurable t U V).const_mul β |>.exp).mul
      ((dTrace_measurable t U V).const_mul β)).aestronglyMeasurable
  have hb : ∀ᵐ a ∂gaugeHaar, ∀ h ∈ Set.Ioo (t-1) (t+1), ‖G h a‖ ≤ E*(192*|β|) := by
    filter_upwards with a h _
    change ‖Real.exp (β*cTrace h U V a)*(β*dTrace h U V a)‖ ≤ _
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (he h a) (slope_bound β h U V a) (abs_nonneg _) (Real.exp_pos _).le
  have hd : ∀ᵐ a ∂gaugeHaar, ∀ h ∈ Set.Ioo (t-1) (t+1), HasDerivAt (F · a) (G h a) h := by
    filter_upwards with a h _
    simpa only [F,G,mul_comm] using ((cTrace_derivative h U V a).const_mul β).exp
  obtain ⟨_,hh⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith) (by linarith)) (Eventually.of_forall hm) hi hg hb
    (integrable_const _) hd
  simpa only [partition,weighted,one_mul,F,G,cTrace,firstJet] using hh

theorem firstJet_derivative (β : ℝ) (U V : State) (t : ℝ) :
    HasDerivAt (firstJet β U V) (secondJet β U V t) t := by
  let F := fun h a => Real.exp (β*cTrace h U V a)*(β*dTrace h U V a)
  let G := fun h a => Real.exp (β*cTrace h U V a)*
    ((β*dTrace h U V a)^2-β*cTrace h U V a)
  let E := Real.exp (192*|β|)
  let B := 192*|β|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have he (h : ℝ) (a : Gauge) : Real.exp (β*cTrace h U V a) ≤ E :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (phase_bound β h U V a))
  have hm (h : ℝ) : AEStronglyMeasurable (F h) gaugeHaar :=
    (((cTrace_measurable h U V).const_mul β |>.exp).mul
      ((dTrace_measurable h U V).const_mul β)).aestronglyMeasurable
  have hi : Integrable (F t) gaugeHaar := by
    apply Integrable.of_bound (hm t) (E*B)
    filter_upwards with a
    change ‖Real.exp (β*cTrace t U V a)*(β*dTrace t U V a)‖ ≤ _
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (he t a) (slope_bound β t U V a) (abs_nonneg _) (Real.exp_pos _).le
  have hg : AEStronglyMeasurable (G t) gaugeHaar :=
    (((cTrace_measurable t U V).const_mul β |>.exp).mul
      ((((dTrace_measurable t U V).const_mul β).pow_const 2).sub
        ((cTrace_measurable t U V).const_mul β))).aestronglyMeasurable
  have hb : ∀ᵐ a ∂gaugeHaar, ∀ h ∈ Set.Ioo (t-1) (t+1), ‖G h a‖ ≤ E*(B^2+B) := by
    filter_upwards with a h _
    change ‖Real.exp (β*cTrace h U V a)*((β*dTrace h U V a)^2-β*cTrace h U V a)‖ ≤ _
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (he h a) (curvature_bound β h U V a) (abs_nonneg _) (Real.exp_pos _).le
  have hd : ∀ᵐ a ∂gaugeHaar, ∀ h ∈ Set.Ioo (t-1) (t+1), HasDerivAt (F · a) (G h a) h := by
    filter_upwards with a h _
    have hh := (((cTrace_derivative h U V a).const_mul β).exp).mul
      ((dTrace_derivative h U V a).const_mul β)
    convert hh using 1 <;> dsimp only [F,G] <;> ring
  obtain ⟨_,hh⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith) (by linarith)) (Eventually.of_forall hm) hi hg hb
    (integrable_const _) hd
  exact hh

theorem partition_second_derivative (β : ℝ) (U V : State) (t : ℝ) :
    HasDerivAt (deriv (fun h => partition β (PeriodicEndpointScore.left h U) V))
      (secondJet β U V t) t := by
  have he : deriv (fun h => partition β (PeriodicEndpointScore.left h U) V)=firstJet β U V :=
    funext (fun h => (partition_derivative β U V h).deriv)
  rw [he]
  exact firstJet_derivative β U V t

private theorem weighted_integrable (β : ℝ) (U V : State) (f : Gauge → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ a, |f a| ≤ M) :
    Integrable (fun a => f a*Real.exp (β*traceSum U V a)) gaugeHaar := by
  apply Integrable.mono' ((exp_integrable β U V).const_mul M)
    (hf.mul ((trace_measurable U V).const_mul β |>.exp)).aestronglyMeasurable
  filter_upwards with a
  change ‖f a*Real.exp (β*traceSum U V a)‖ ≤ _
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hb a) (Real.exp_pos _).le

theorem firstJet_weighted (β : ℝ) (U V : State) (h : ℝ) :
    firstJet β U V h=β*weighted β (PeriodicEndpointScore.left h U) V (dTrace h U V) := by
  unfold firstJet weighted
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with a
  dsimp only [cTrace]
  ring

theorem secondJet_weighted (β : ℝ) (U V : State) (h : ℝ) :
    secondJet β U V h =
      β^2*weighted β (PeriodicEndpointScore.left h U) V (fun a => (dTrace h U V a)^2)-
        β*weighted β (PeriodicEndpointScore.left h U) V (cTrace h U V) := by
  have hd := weighted_integrable β (PeriodicEndpointScore.left h U) V
    (fun a => (dTrace h U V a)^2) ((dTrace_measurable h U V).pow_const 2) (192^2)
    (fun a => by simpa only [abs_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (dTrace_bound h U V a) 2)
  have hc := weighted_integrable β (PeriodicEndpointScore.left h U) V
    (cTrace h U V) (cTrace_measurable h U V) 192 (cTrace_bound h U V)
  unfold secondJet weighted
  rw [← integral_const_mul,← integral_const_mul,← integral_sub (hd.const_mul _) (hc.const_mul _)]
  apply integral_congr_ae
  filter_upwards with a
  dsimp only [cTrace]
  ring

def firstPolynomial (β : ℝ) (U V : State) (h : ℝ) : ℝ :=
  β*weightedPolynomial 4 β (PeriodicEndpointScore.left h U) V (dTrace h U V)

def secondPolynomial (β : ℝ) (U V : State) (h : ℝ) : ℝ :=
  β^2*weightedPolynomial 3 β (PeriodicEndpointScore.left h U) V (fun a => (dTrace h U V a)^2)-
    β*weightedPolynomial 4 β (PeriodicEndpointScore.left h U) V (cTrace h U V)

theorem firstJet_taylor_bound (β : ℝ) (U V : State) (h : ℝ) :
    |firstJet β U V h-firstPolynomial β U V h| ≤ 192*|β| *errorBound 4 β := by
  have hh := weighted_taylor_bound 4 β (PeriodicEndpointScore.left h U) V
    (dTrace h U V) (dTrace_measurable h U V) 192 (by norm_num) (dTrace_bound h U V)
  rw [firstJet_weighted,firstPolynomial,← mul_sub,abs_mul]
  calc
    _ ≤ |β| *(192*errorBound 4 β) := mul_le_mul_of_nonneg_left hh (abs_nonneg β)
    _ = _ := by ring

theorem secondJet_taylor_bound (β : ℝ) (U V : State) (h : ℝ) :
    |secondJet β U V h-secondPolynomial β U V h| ≤
      β^2*192^2*errorBound 3 β+192*|β| *errorBound 4 β := by
  have hdb (a : Gauge) : |(dTrace h U V a)^2| ≤ (192 : ℝ)^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (dTrace_bound h U V a) 2
  have hd := weighted_taylor_bound 3 β (PeriodicEndpointScore.left h U) V
    (fun a => (dTrace h U V a)^2) ((dTrace_measurable h U V).pow_const 2) (192^2)
    (by positivity) hdb
  have hc := weighted_taylor_bound 4 β (PeriodicEndpointScore.left h U) V
    (cTrace h U V) (cTrace_measurable h U V) 192 (by norm_num) (cTrace_bound h U V)
  let A := weighted β (PeriodicEndpointScore.left h U) V (fun a => (dTrace h U V a)^2)-
    weightedPolynomial 3 β (PeriodicEndpointScore.left h U) V (fun a => (dTrace h U V a)^2)
  let B := weighted β (PeriodicEndpointScore.left h U) V (cTrace h U V)-
    weightedPolynomial 4 β (PeriodicEndpointScore.left h U) V (cTrace h U V)
  have he : secondJet β U V h-secondPolynomial β U V h=β^2*A-β*B := by
    rw [secondJet_weighted]
    unfold secondPolynomial A B
    ring
  rw [he]
  calc
    _ ≤ |β^2*A|+|β*B| := abs_sub _ _
    _ = β^2*|A|+|β| *|B| := by rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg β)]
    _ ≤ β^2*(192^2*errorBound 3 β)+|β| *(192*errorBound 4 β) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hd (sq_nonneg β))
        (mul_le_mul_of_nonneg_left hc (abs_nonneg β))
    _ = _ := by ring

def logSlope (β : ℝ) (U V : State) (h : ℝ) : ℝ :=
  firstJet β U V h/partition β (PeriodicEndpointScore.left h U) V

def logCurvature (β : ℝ) (U V : State) (h : ℝ) : ℝ :=
  secondJet β U V h/partition β (PeriodicEndpointScore.left h U) V-
    (firstJet β U V h/partition β (PeriodicEndpointScore.left h U) V)^2

theorem log_partition_derivative (β : ℝ) (U V : State) (h : ℝ) :
    HasDerivAt (fun t => Real.log (partition β (PeriodicEndpointScore.left t U) V))
      (logSlope β U V h) h :=
  (partition_derivative β U V h).log (partition_pos β _ V).ne'

theorem logSlope_derivative (β : ℝ) (U V : State) (h : ℝ) :
    HasDerivAt (logSlope β U V) (logCurvature β U V h) h := by
  have hn := (partition_pos β (PeriodicEndpointScore.left h U) V).ne'
  have hd := (firstJet_derivative β U V h).div (partition_derivative β U V h) hn
  have he : logCurvature β U V h =
      (secondJet β U V h*partition β (PeriodicEndpointScore.left h U) V-
        firstJet β U V h*firstJet β U V h)/partition β (PeriodicEndpointScore.left h U) V^2 := by
    unfold logCurvature
    field_simp [hn]
    <;> ring
  rw [he]
  exact hd

/-- Actual Wilson log-kernel seam contrast: both boundary derivatives and the
moving temporal normalizers are retained; spatial prefactors cancel by proof. -/
theorem kernel_log_second (β : ℝ) (U V : State) (t : ℝ) :
    HasDerivAt (deriv (fun h =>
      Real.log (kernel β (PeriodicEndpointScore.left h U) V)-
        Real.log (kernel β (PeriodicEndpointScore.left h U) (PeriodicCenterSeam.flip 1 V))))
      (logCurvature β U V t-logCurvature β U (PeriodicCenterSeam.flip 1 V) t) t := by
  have he : (fun h => Real.log (kernel β (PeriodicEndpointScore.left h U) V)-
      Real.log (kernel β (PeriodicEndpointScore.left h U) (PeriodicCenterSeam.flip 1 V))) =
      (fun h => Real.log (partition β (PeriodicEndpointScore.left h U) V)-
        Real.log (partition β (PeriodicEndpointScore.left h U) (PeriodicCenterSeam.flip 1 V))) :=
    funext (fun h => kernel_log_contrast β (PeriodicEndpointScore.left h U) V)
  rw [he]
  have hd : deriv (fun h => Real.log (partition β (PeriodicEndpointScore.left h U) V)-
      Real.log (partition β (PeriodicEndpointScore.left h U) (PeriodicCenterSeam.flip 1 V))) =
      (fun h => logSlope β U V h-logSlope β U (PeriodicCenterSeam.flip 1 V) h) :=
    funext (fun h => ((log_partition_derivative β U V h).sub
      (log_partition_derivative β U (PeriodicCenterSeam.flip 1 V) h)).deriv)
  rw [hd]
  exact (logSlope_derivative β U V t).sub
    (logSlope_derivative β U (PeriodicCenterSeam.flip 1 V) t)

theorem kernel_contrast_bound (β h : ℝ) :
    |kernel β (PeriodicTemporalCycleMoment.orbit h) 1-
      kernel β (PeriodicTemporalCycleMoment.orbit h) (PeriodicCenterSeam.flip 1 1)-
        prefactor β (PeriodicTemporalCycleMoment.orbit h) 1*(β^4/2*Real.cos (4*h))| ≤
          2*prefactor β (PeriodicTemporalCycleMoment.orbit h) 1*errorBound 5 β := by
  rw [kernel_factor,kernel_factor,prefactor_twist]
  have he : prefactor β (PeriodicTemporalCycleMoment.orbit h) 1*
      partition β (PeriodicTemporalCycleMoment.orbit h) 1-
      prefactor β (PeriodicTemporalCycleMoment.orbit h) 1*
      partition β (PeriodicTemporalCycleMoment.orbit h) (PeriodicCenterSeam.flip 1 1)-
      prefactor β (PeriodicTemporalCycleMoment.orbit h) 1*(β^4/2*Real.cos (4*h)) =
      prefactor β (PeriodicTemporalCycleMoment.orbit h) 1*
      (partition β (PeriodicTemporalCycleMoment.orbit h) 1-
        partition β (PeriodicTemporalCycleMoment.orbit h) (PeriodicCenterSeam.flip 1 1)-
          β^4/2*Real.cos (4*h)) := by ring
  rw [he,abs_mul,abs_of_pos (prefactor_pos β _ _)]
  exact (mul_le_mul_of_nonneg_left (partition_contrast_bound β h)
    (prefactor_pos β _ _).le).trans_eq (by ring)

def relativeError (β : ℝ) : ℝ := 2*192^5*|β| *Real.exp (192*|β|)

theorem error_fifth_factor (β : ℝ) : 2*errorBound 5 β=β^4*relativeError β := by
  have h4 : |β|^4=β^4 := by
    calc
      _ = (|β|^2)^2 := by ring
      _ = (β^2)^2 := by rw [sq_abs]
      _ = _ := by ring
  have h5 : |β|^5=β^4*|β| := by rw [pow_succ,h4]
  simp only [errorBound,relativeError,mul_pow,h5]
  ring

theorem relativeError_tendsto : Tendsto relativeError (𝓝 0) (𝓝 0) := by
  have hc : Continuous relativeError := by unfold relativeError; fun_prop
  simpa only [relativeError,abs_zero,mul_zero,Real.exp_zero,zero_mul] using hc.tendsto 0

theorem kernel_separation (β h : ℝ) (hβ : β ≠ 0)
    (he : relativeError β < Real.cos (4*h)/2) :
    kernel β (PeriodicTemporalCycleMoment.orbit h) (PeriodicCenterSeam.flip 1 1) <
      kernel β (PeriodicTemporalCycleMoment.orbit h) 1 := by
  let U := PeriodicTemporalCycleMoment.orbit h
  let T := PeriodicCenterSeam.flip 1 (1 : State)
  have hp : 0 < β^4 := by positivity
  have hh := partition_contrast_bound β h
  rw [error_fifth_factor] at hh
  have ha := (abs_le.mp hh).1
  have hc : β^4*relativeError β < β^4*(Real.cos (4*h)/2) := mul_lt_mul_of_pos_left he hp
  have hd : partition β U T < partition β U 1 := by dsimp only [U,T]; nlinarith
  rw [kernel_factor,kernel_factor,prefactor_twist]
  exact mul_lt_mul_of_pos_left hd (prefactor_pos β U 1)

/-- One punctured coupling neighborhood works for EVERY h in the stated
cosine window. This is a fixed-volume kernel comparison only. -/
theorem eventual_kernel_separation : ∀ᶠ β : ℝ in 𝓝[≠] 0, ∀ h : ℝ,
    (1/2 : ℝ) ≤ Real.cos (4*h) →
    kernel β (PeriodicTemporalCycleMoment.orbit h) (PeriodicCenterSeam.flip 1 1) <
      kernel β (PeriodicTemporalCycleMoment.orbit h) 1 := by
  have he : ∀ᶠ β : ℝ in 𝓝 0, relativeError β < 1/4 :=
    relativeError_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/4))
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with β hb hn
  intro h hh
  apply kernel_separation β h
  · simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hn
  · linarith

theorem kernel_separation_reversed (β h : ℝ) (hβ : β ≠ 0)
    (he : relativeError β < -Real.cos (4*h)/2) :
    kernel β (PeriodicTemporalCycleMoment.orbit h) 1 <
      kernel β (PeriodicTemporalCycleMoment.orbit h) (PeriodicCenterSeam.flip 1 1) := by
  let U := PeriodicTemporalCycleMoment.orbit h
  let T := PeriodicCenterSeam.flip 1 (1 : State)
  have hp : 0 < β^4 := by positivity
  have hh := partition_contrast_bound β h
  rw [error_fifth_factor] at hh
  have ha := (abs_le.mp hh).2
  have hc : β^4*relativeError β < β^4*(-Real.cos (4*h)/2) := mul_lt_mul_of_pos_left he hp
  have hd : partition β U 1 < partition β U T := by dsimp only [U,T]; nlinarith
  rw [kernel_factor,kernel_factor,prefactor_twist]
  exact mul_lt_mul_of_pos_left hd (prefactor_pos β U 1)

theorem eventual_kernel_sign_pattern : ∀ᶠ β : ℝ in 𝓝[≠] 0,
    kernel β (PeriodicTemporalCycleMoment.orbit 0) (PeriodicCenterSeam.flip 1 1) <
      kernel β (PeriodicTemporalCycleMoment.orbit 0) 1 ∧
    kernel β (PeriodicTemporalCycleMoment.orbit (Real.pi/4)) 1 <
      kernel β (PeriodicTemporalCycleMoment.orbit (Real.pi/4)) (PeriodicCenterSeam.flip 1 1) ∧
    kernel β (PeriodicTemporalCycleMoment.orbit (-Real.pi/4)) 1 <
      kernel β (PeriodicTemporalCycleMoment.orbit (-Real.pi/4)) (PeriodicCenterSeam.flip 1 1) := by
  have he : ∀ᶠ β : ℝ in 𝓝 0, relativeError β < 1/4 :=
    relativeError_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/4))
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with β hb hn
  have hβ : β ≠ 0 := by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hn
  refine ⟨kernel_separation β 0 hβ ?_,kernel_separation_reversed β (Real.pi/4) hβ ?_,
    kernel_separation_reversed β (-Real.pi/4) hβ ?_⟩
  · norm_num
    linarith
  · rw [show (4 : ℝ)*(Real.pi/4)=Real.pi by ring,Real.cos_pi]
    linarith
  · rw [show (4 : ℝ)*(-Real.pi/4)= -Real.pi by ring,Real.cos_neg,Real.cos_pi]
    linarith

def orbitLogContrast (β h : ℝ) : ℝ :=
  Real.log (kernel β (PeriodicTemporalCycleMoment.orbit h) 1)-
    Real.log (kernel β (PeriodicTemporalCycleMoment.orbit h) (PeriodicCenterSeam.flip 1 1))

theorem eventual_log_sign_pattern : ∀ᶠ β : ℝ in 𝓝[≠] 0,
    0 < orbitLogContrast β 0 ∧ orbitLogContrast β (Real.pi/4) < 0 ∧
      orbitLogContrast β (-Real.pi/4) < 0 := by
  filter_upwards [eventual_kernel_sign_pattern] with β hh
  unfold orbitLogContrast
  exact ⟨sub_pos.mpr (Real.log_lt_log (kernel_positive β _ _) hh.1),
    sub_neg.mpr (Real.log_lt_log (kernel_positive β _ _) hh.2.1),
    sub_neg.mpr (Real.log_lt_log (kernel_positive β _ _) hh.2.2)⟩

theorem orbitLog_first (β h : ℝ) :
    HasDerivAt (orbitLogContrast β)
      (logSlope β PeriodicEndpointFibreWitness.leftEndpoint 1 h-
        logSlope β PeriodicEndpointFibreWitness.leftEndpoint (PeriodicCenterSeam.flip 1 1) h) h := by
  have he : orbitLogContrast β = (fun t =>
      Real.log (partition β (PeriodicTemporalCycleMoment.orbit t) 1)-
        Real.log (partition β (PeriodicTemporalCycleMoment.orbit t) (PeriodicCenterSeam.flip 1 1))) :=
    funext (fun t => kernel_log_contrast β (PeriodicTemporalCycleMoment.orbit t) 1)
  rw [he]
  exact (log_partition_derivative β PeriodicEndpointFibreWitness.leftEndpoint 1 h).sub
    (log_partition_derivative β PeriodicEndpointFibreWitness.leftEndpoint (PeriodicCenterSeam.flip 1 1) h)

theorem orbitLog_second (β h : ℝ) :
    HasDerivAt (deriv (orbitLogContrast β))
      (logCurvature β PeriodicEndpointFibreWitness.leftEndpoint 1 h-
        logCurvature β PeriodicEndpointFibreWitness.leftEndpoint (PeriodicCenterSeam.flip 1 1) h) h :=
  kernel_log_second β PeriodicEndpointFibreWitness.leftEndpoint 1 h

private theorem interior_negative_curvature (F : ℝ → ℝ) (a : ℝ) (ha : 0<a)
    (hf : Differentiable ℝ F) (hdf : Differentiable ℝ (deriv F))
    (hl : F (-a)<F 0) (hr : F a<F 0) :
    ∃ t ∈ Set.Ioo (-a) a, deriv (deriv F) t<0 := by
  obtain ⟨x,hx,hdx⟩ := exists_deriv_eq_slope F (a := -a) (b := 0) (by linarith)
    hf.continuous.continuousOn hf.differentiableOn
  obtain ⟨y,hy,hdy⟩ := exists_deriv_eq_slope F (a := 0) (b := a) ha
    hf.continuous.continuousOn hf.differentiableOn
  have hxpos : 0 < deriv F x := by rw [hdx]; exact div_pos (sub_pos.mpr hl) (by linarith)
  have hyneg : deriv F y < 0 := by rw [hdy]; exact div_neg_of_neg_of_pos (sub_neg.mpr hr) (by simpa only [sub_zero] using ha)
  have hxy : x<y := by linarith [hx.2,hy.1]
  obtain ⟨t,ht,hdt⟩ := exists_deriv_eq_slope (deriv F) (a := x) (b := y) hxy
    hdf.continuous.continuousOn hdf.differentiableOn
  refine ⟨t,⟨by linarith [hx.1,ht.1],by linarith [hy.2,ht.2]⟩,?_⟩
  rw [hdt]
  exact div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr hxy)

/-- A genuine negative curvature contrast for the ACTUAL single-Wilson log
kernels, with temporal normalization retained, somewhere on the original quarter-turn orbit at small nonzero
coupling. No claim about h=0, physicalSecond, or a uniform lower frame is made. -/
theorem eventual_negative_log_curvature : ∀ᶠ β : ℝ in 𝓝[≠] 0,
    ∃ t ∈ Set.Ioo (-Real.pi/4) (Real.pi/4),
      logCurvature β PeriodicEndpointFibreWitness.leftEndpoint 1 t-
        logCurvature β PeriodicEndpointFibreWitness.leftEndpoint (PeriodicCenterSeam.flip 1 1) t < 0 := by
  filter_upwards [eventual_log_sign_pattern] with β hh
  have hf : Differentiable ℝ (orbitLogContrast β) := fun t => (orbitLog_first β t).differentiableAt
  have hdf : Differentiable ℝ (deriv (orbitLogContrast β)) :=
    fun t => (orbitLog_second β t).differentiableAt
  obtain ⟨t,ht,hneg⟩ := interior_negative_curvature (orbitLogContrast β) (Real.pi/4)
    (by positivity) hf hdf (by simpa only [neg_div] using hh.2.2.trans hh.1)
    (hh.2.1.trans hh.1)
  refine ⟨t,by simpa only [neg_div] using ht,?_⟩
  rwa [(orbitLog_second β t).deriv] at hneg

end OperatorDerivativeRewrite.Foundation.PeriodicTemporalLaplaceContrast
