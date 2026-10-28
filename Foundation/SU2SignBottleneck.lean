import Foundation.SU2VariationalGap
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.SU2CoupledLoopResponse
open OperatorDerivativeRewrite.Foundation.SU2LoopEquilibrium
open OperatorDerivativeRewrite.Foundation.SU2StrongCouplingCovariance
open OperatorDerivativeRewrite.Foundation.SU2VariationalGap
namespace OperatorDerivativeRewrite.Foundation.SU2SignBottleneck

def phase (x : ℝ) : ℝ := if 0 < x then 1 else if x < 0 then -1 else 0
private theorem phase_bound (x : ℝ) : |phase x| ≤ 1 := by
  unfold phase
  split_ifs <;> norm_num
private theorem phase_neg (x : ℝ) : phase (-x) = -phase x := by
  unfold phase
  split_ifs <;> simp_all <;> linarith
private theorem phase_measurable : Measurable phase := by
  unfold phase
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const)
private theorem phase_square_dominates (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    x*y ≤ phase x ^ 2 := by
  have hp : x*y ≤ 1 := (le_abs_self _).trans (by
    rw [abs_mul]; simpa using (mul_le_mul hx hy (abs_nonneg _) (by norm_num)))
  unfold phase
  split_ifs with hpos hneg
  · simpa using hp
  · simpa using hp
  · have : x = 0 := by linarith
    simp [this]
private theorem phase_difference_bound (x y : ℝ) :
    (phase x - phase y)^2 ≤ if x*y ≤ 0 then 4 else 0 := by
  unfold phase
  split_ifs <;> simp_all <;> nlinarith

def observable (C : SU2) : ℝ := phase (halfTrace C)
def variance (r : ℝ) : ℝ := ∫ p, observable p.1 ^ 2 ∂coupledLaw r
def dirichlet (r : ℝ) : ℝ := (∫ p, (observable p.1 - observable p.2)^2 ∂coupledLaw r) / 2
private theorem observable_measurable : Measurable observable := phase_measurable.comp halfTrace_measurable
theorem observable_conjugate (U C : SU2) : observable (U*C*U⁻¹) = observable C := by
  simp only [observable, halfTrace_conjugate]
private theorem observable_bound (C : SU2) : |observable C| ≤ 1 := phase_bound _
private theorem bounded_integrable (r : ℝ) (f : SU2 × SU2 → ℝ)
    (hf : Measurable f) (b : ℝ) (hb : ∀ p, |f p| ≤ b) : Integrable f (coupledLaw r) := by
  letI := coupledLaw_probability r
  apply Integrable.mono' (integrable_const b) hf.aestronglyMeasurable
  filter_upwards with p
  simpa only [Real.norm_eq_abs] using hb p
private theorem square_bound (C : SU2) : |observable C ^ 2| ≤ 1 := by
  have h := abs_le.mp (observable_bound C)
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith
private theorem square_integrable (r : ℝ) : Integrable (fun p => observable p.1 ^ 2) (coupledLaw r) :=
  bounded_integrable r _ ((observable_measurable.comp measurable_fst).pow_const 2) 1
    (fun p => square_bound p.1)
private theorem difference_integrable (r : ℝ) :
    Integrable (fun p => (observable p.1 - observable p.2)^2) (coupledLaw r) := by
  apply bounded_integrable r _
    (((observable_measurable.comp measurable_fst).sub (observable_measurable.comp measurable_snd)).pow_const 2) 4
  intro p
  have hx := abs_le.mp (observable_bound p.1)
  have hy := abs_le.mp (observable_bound p.2)
  rw [abs_of_nonneg (sq_nonneg _)]
  change (observable p.1 - observable p.2)^2 ≤ 4
  nlinarith

theorem mean_zero (r : ℝ) : (∫ C, observable C ∂equilibriumLaw r) = 0 := by
  rw [equilibriumLaw_eq_fst]
  change (∫ C, observable C ∂(coupledLaw r).map Prod.fst) = 0
  rw [integral_map measurable_fst.aemeasurable observable_measurable.aestronglyMeasurable]
  apply center_odd_mean_zero r _ (observable_measurable.comp measurable_fst)
    (fun p => observable_bound p.1)
  intro p
  change phase (halfTrace (SU2StapleExtremes.minusOne * p.1)) = -phase (halfTrace p.1)
  rw [halfTrace_center_neg, phase_neg]

theorem variance_tendsto_one : Tendsto variance atTop (𝓝 1) := by
  have hl (r : ℝ) : lagCov r 1 ≤ variance r := by
    rw [lagCov_one, corr_eq_interaction_mean]
    apply integral_mono ?_ (square_integrable r)
    · intro p
      exact phase_square_dominates _ _ (halfTrace_bound p.1) (halfTrace_bound p.2)
    · apply bounded_integrable r _
        ((halfTrace_measurable.comp measurable_fst).mul (halfTrace_measurable.comp measurable_snd)) 1
      intro p
      exact (abs_mul (F p) (G p)).trans_le (by
        simpa [F,G] using mul_le_mul (halfTrace_bound p.1) (halfTrace_bound p.2)
          (abs_nonneg _) (by norm_num))
  have hu (r : ℝ) : variance r ≤ 1 := by
    letI := coupledLaw_probability r
    have h := integral_mono (square_integrable r) (integrable_const (1:ℝ))
      (fun p => (le_abs_self _).trans (square_bound p.1))
    simpa [variance] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le stationary_lag_one_cov_tendsto_one
    tendsto_const_nhds hl hu

theorem dirichlet_exponential_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 ≤ r → dirichlet r ≤ c * Real.exp (-r/2) := by
  obtain ⟨c,hc,ht⟩ := nonpositive_interaction_bound
  refine ⟨2*c, by positivity, ?_⟩
  intro r hr
  letI := coupledLaw_probability r
  let S : Set (SU2 × SU2) := {p | X p ≤ 0}
  have hs : MeasurableSet S := measurableSet_le
    ((halfTrace_measurable.comp measurable_fst).mul (halfTrace_measurable.comp measurable_snd)) measurable_const
  have hb : (∫ p, (observable p.1-observable p.2)^2 ∂coupledLaw r) ≤
      ∫ p, S.indicator (fun _ => (4:ℝ)) p ∂coupledLaw r := by
    apply integral_mono (difference_integrable r) ((integrable_const (4:ℝ)).indicator hs)
    intro p
    change (observable p.1 - observable p.2)^2 ≤ S.indicator (fun _ => (4:ℝ)) p
    have h := phase_difference_bound (halfTrace p.1) (halfTrace p.2)
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp]
      have hx : halfTrace p.1 * halfTrace p.2 ≤ 0 := hp
      change (phase (halfTrace p.1) - phase (halfTrace p.2))^2 ≤ 4
      rw [if_pos hx] at h
      exact h
    · rw [Set.indicator_of_notMem hp]
      have hx : ¬halfTrace p.1 * halfTrace p.2 ≤ 0 := hp
      change (phase (halfTrace p.1) - phase (halfTrace p.2))^2 ≤ 0
      rw [if_neg hx] at h
      exact h
  rw [integral_indicator hs, integral_const] at hb
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul] at hb
  have ht' := ht r hr
  change (coupledLaw r).real S ≤ _ at ht'
  dsimp [dirichlet]
  simp only [Measure.real] at ht'
  nlinarith


theorem observable_memLp (r : ℝ) : MemLp observable 2 (equilibriumLaw r) := by
  letI := equilibriumLaw_probability r
  apply MemLp.of_bound observable_measurable.aestronglyMeasurable 1
  filter_upwards with C
  simpa only [Real.norm_eq_abs] using observable_bound C

def vector (r : ℝ) : StateL2 r := (observable_memLp r).toLp observable

theorem vector_mean (r : ℝ) : (∫ C, vector r C ∂equilibriumLaw r) = 0 := by
  unfold vector
  rw [integral_congr_ae (MemLp.coeFn_toLp (observable_memLp r))]
  exact mean_zero r

theorem vector_square (r : ℝ) : inner ℝ (vector r) (vector r) = variance r := by
  have he : (∫ C, observable C ^ 2 ∂equilibriumLaw r) = variance r := by
    rw [equilibriumLaw_eq_fst]
    change (∫ C, observable C ^ 2 ∂(coupledLaw r).map Prod.fst) = _
    rw [integral_map measurable_fst.aemeasurable (observable_measurable.pow_const 2).aestronglyMeasurable]
    rfl
  rw [L2.inner_def, ← he]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (observable_memLp r)] with C hC
  change vector r C = observable C at hC
  rw [hC]
  simp [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem vector_energy (r : ℝ) :
    inner ℝ (vector r) (vector r) - inner ℝ (operator r (vector r)) (vector r) = dirichlet r := by
  have hp : inner ℝ (operator r (vector r)) (vector r) =
      ∫ p, observable p.1 * observable p.2 ∂coupledLaw r := by
    rw [operator_pairing]
    apply integral_congr_ae
    have hl := (left_preserving r).quasiMeasurePreserving.ae_eq_comp
      (MemLp.coeFn_toLp (observable_memLp r))
    have hr := (right_preserving r).quasiMeasurePreserving.ae_eq_comp
      (MemLp.coeFn_toLp (observable_memLp r))
    filter_upwards [hl,hr] with p h₁ h₂
    change vector r p.1 = observable p.1 at h₁
    change vector r p.2 = observable p.2 at h₂
    rw [h₁,h₂]
  have hs : (∫ p, observable p.2 ^ 2 ∂coupledLaw r) = variance r := by
    have he := integral_map (μ := coupledLaw r) measurable_swap.aemeasurable
      (((observable_measurable.comp measurable_fst).pow_const 2).aestronglyMeasurable)
    rw [coupledLaw_exchangeable] at he
    exact he.symm
  have hi₂ : Integrable (fun p => observable p.2 ^ 2) (coupledLaw r) :=
    bounded_integrable r _ ((observable_measurable.comp measurable_snd).pow_const 2) 1
      (fun p => square_bound p.2)
  have hip : Integrable (fun p => observable p.1 * observable p.2) (coupledLaw r) := by
    apply bounded_integrable r _ ((observable_measurable.comp measurable_fst).mul
      (observable_measurable.comp measurable_snd)) 1
    intro p
    change |observable p.1 * observable p.2| ≤ 1
    rw [abs_mul]
    simpa using mul_le_mul (observable_bound p.1) (observable_bound p.2) (abs_nonneg _) (by norm_num)
  have he : (fun p : SU2 × SU2 => (observable p.1-observable p.2)^2) =
      (fun p => observable p.1^2+observable p.2^2-2*(observable p.1*observable p.2)) := by
    funext p
    ring
  rw [vector_square, hp, dirichlet, he]
  have hi := integral_sub ((square_integrable r).add hi₂) (hip.const_mul 2)
  change (∫ p, observable p.1^2+observable p.2^2-2*(observable p.1*observable p.2) ∂coupledLaw r) = _ at hi
  rw [hi]
  change variance r - _ = ((∫ p, observable p.1^2+observable p.2^2 ∂coupledLaw r) -
    (∫ p, 2*(observable p.1*observable p.2) ∂coupledLaw r))/2
  rw [integral_add (square_integrable r) hi₂, integral_const_mul, hs]
  change variance r - _ = (variance r + variance r - _)/2
  ring

/-- A centered, nonzero actual stationary L2 test has an exponentially small Rayleigh quotient.
This is an upper obstruction, not an optimal asymptotic or a claim about the 4D Wilson transfer. -/
theorem exponential_variational_obstruction :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in atTop,
      (∫ C, vector r C ∂equilibriumLaw r) = 0 ∧
      0 < inner ℝ (vector r) (vector r) ∧
      inner ℝ (vector r) (vector r) - inner ℝ (operator r (vector r)) (vector r) ≤
        (c * Real.exp (-r/2)) * inner ℝ (vector r) (vector r) := by
  obtain ⟨c,hc,hb⟩ := dirichlet_exponential_bound
  refine ⟨2*c, by positivity, ?_⟩
  have hv := (tendsto_order.mp variance_tendsto_one).1 (1/2) (by norm_num)
  filter_upwards [hv, eventually_ge_atTop (0:ℝ)] with r hvr hr
  refine ⟨vector_mean r, ?_, ?_⟩
  · rw [vector_square]; linarith
  · rw [vector_energy, vector_square]
    have h := hb r hr
    have he := Real.exp_pos (-r/2)
    have hm := mul_nonneg (mul_pos hc he).le (show 0 ≤ 2*variance r-1 by linarith)
    nlinarith

end OperatorDerivativeRewrite.Foundation.SU2SignBottleneck
