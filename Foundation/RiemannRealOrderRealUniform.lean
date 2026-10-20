import Foundation.RiemannRealOrderFourierDecay

/-! Uniform order convergence on the entire REAL frequency axis, with
joint order/frequency decay. No control of nonreal zeros follows from a
real-axis estimate alone. Time is fixed in every limit below. -/
noncomputable section
open MeasureTheory Set Filter Metric Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderRealUniform
open RiemannRealOrderFlow RiemannRealOrderLimit RiemannRealOrderFourierDecay
open RiemannQuarticFlow (halfLine)

theorem jet_difference_bound_real (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (j : ℕ) (t x : ℝ) :
    ‖jet a j t (x : ℂ)-jet b j t (x : ℂ)‖ ≤
      ∫ u : ℝ, |weighted a j t 0 u-weighted b j t 0 u| ∂halfLine := by
  have hmajor : Integrable (fun u : ℝ => |weighted a j t 0 u-weighted b j t 0 u|) halfLine := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using
      ((weighted_integrable a ha j t 0).sub (weighted_integrable b hb j t 0)).norm
  have hpoint : ∀ᵐ u : ℝ ∂halfLine,
      ‖integrand a j t (x : ℂ) u-integrand b j t (x : ℂ) u‖ ≤
        |weighted a j t 0 u-weighted b j t 0 u| := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have hu0 : (0 : ℝ) ≤ u := hu
    have he : integrand a j t (x : ℂ) u-integrand b j t (x : ℂ) u =
        ((weighted a 0 t 0 u-weighted b 0 t 0 u : ℝ) : ℂ)*
          (I*(u : ℂ))^j*Complex.exp (I*(u : ℂ)*(x : ℂ)) := by
      simp only [integrand,Complex.ofReal_sub]
      ring
    have hp : ‖Complex.exp (I*(u : ℂ)*(x : ℂ))‖ = 1 := by
      simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
    have hid : weighted a j t 0 u-weighted b j t 0 u =
        (weighted a 0 t 0 u-weighted b 0 t 0 u)*u^j := by
      simp only [weighted,pow_zero,one_mul,zero_mul,add_zero]
      ring
    simp only [he,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_I,one_mul,hp,mul_one,abs_of_nonneg hu0]
    rw [hid,abs_mul,abs_of_nonneg (pow_nonneg hu0 j)]
  have h := norm_integral_le_of_norm_le hmajor hpoint
  change ‖(∫ u : ℝ, integrand a j t (x : ℂ) u ∂halfLine)-
    (∫ u : ℝ, integrand b j t (x : ℂ) u ∂halfLine)‖ ≤ _
  rw [← integral_sub (integrand_integrable a ha j t (x : ℂ))
    (integrand_integrable b hb j t (x : ℂ))]
  exact h

theorem jet_order_tendsto_uniformly_real (a : ℝ) (ha : 0 < a) (j : ℕ) (t : ℝ) :
    TendstoUniformly (fun b : ℝ => fun x : ℝ => jet b j t (x : ℂ))
      (fun x : ℝ => jet a j t (x : ℂ)) (𝓝 a) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(weighted_difference_integral_tendsto_zero a ha j t 0 (by norm_num)).eventually
    (gt_mem_nhds hε),Ioi_mem_nhds ha] with b he hb
  intro x
  rw [dist_eq_norm,norm_sub_rev]
  exact (jet_difference_bound_real b a hb.le ha.le j t x).trans_lt he

theorem flow_order_tendsto_uniformly_real (a : ℝ) (ha : 0 < a) (t : ℝ) :
    TendstoUniformly (fun b : ℝ => fun x : ℝ => flow b t (x : ℂ))
      (fun x : ℝ => flow a t (x : ℂ)) (𝓝 a) := by
  have hj := jet_order_tendsto_uniformly_real a ha 0 t
  rw [Metric.tendstoUniformly_iff] at hj ⊢
  intro ε hε
  filter_upwards [hj ε hε] with b hb
  intro x
  have hp := hb x
  have hn := hb (-x)
  rw [dist_eq_norm,norm_sub_rev] at hp hn ⊢
  simp only [Complex.ofReal_neg] at hn
  have hid : flow b t (x : ℂ)-flow a t (x : ℂ) =
      ((jet b 0 t (x : ℂ)-jet a 0 t (x : ℂ))+
        (jet b 0 t (-(x : ℂ))-jet a 0 t (-(x : ℂ))))/2 := by
    unfold flow
    ring
  rw [hid,norm_div,Complex.norm_ofNat]
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  linarith [norm_add_le (jet b 0 t (x : ℂ)-jet a 0 t (x : ℂ))
    (jet b 0 t (-(x : ℂ))-jet a 0 t (-(x : ℂ)))]

theorem uniform_quadratic_limit_from_above (t : ℝ) :
    TendstoUniformly (fun a : ℝ => fun x : ℝ => flow a t (x : ℂ))
      (fun x : ℝ => RiemannEvenFlow.flow 1 t (x : ℂ)) (𝓝[Ioi (1 : ℝ)] 1) := by
  have h : TendstoUniformly (fun a : ℝ => fun x : ℝ => flow a t (x : ℂ))
      (fun x : ℝ => flow 1 t (x : ℂ)) (𝓝[Ioi (1 : ℝ)] 1) := by
    intro V hV
    exact (flow_order_tendsto_uniformly_real 1 (by norm_num) t V hV).filter_mono nhdsWithin_le_nhds
  have he : flow (1 : ℝ) t = RiemannEvenFlow.flow 1 t := by
    funext z
    simpa only [Nat.cast_one] using flow_nat 1 t z
  simpa only [he] using h

theorem joint_order_real_frequency_decay (a : ℝ) (ha : 0 < a) (t : ℝ) :
    Tendsto (fun p : ℝ × ℝ => flow p.1 t (p.2 : ℂ))
      ((𝓝 a) ×ˢ (cocompact ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ho := (Metric.tendstoUniformly_iff.mp (flow_order_tendsto_uniformly_real a ha t))
    (ε/2) (half_pos hε)
  have hx := (Metric.tendsto_nhds.mp (flow_real_genuine_and_decay a ha.le t).2)
    (ε/2) (half_pos hε)
  filter_upwards [ho.prod_mk hx] with p hp
  exact (dist_triangle _ (flow a t (p.2 : ℂ)) 0).trans_lt
    (by
      have horder := hp.1 p.2
      rw [dist_comm] at horder
      linarith [hp.2])

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderRealUniform
