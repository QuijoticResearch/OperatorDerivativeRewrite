import Foundation.StochasticCauchyDiskCompletion
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyDiskDerivative
open StochasticCauchyDiskCompletion InfiniteGaussian StochasticCauchyParameterizedObstruction
open StochasticCauchyJointPastIntegral StochasticCauchyComplexChannels StochasticCauchyPhysicalInput
open StochasticCauchyExponentialInput StochasticCauchyExitClock StochasticCauchyStoppedPolynomialIto
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct
private abbrev ρ (T : ℝ≥0) := (timeMeasure T).prod gaussianProduct

private def physicalField (T : ℝ≥0) (u : ComplexInput T) : Lp ℂ 2 (ρ T) :=
  ComplexL2Isometry.combine (ρ T) (fieldEmbedding T (realInput T u)) (fieldEmbedding T (imagInput T u))

private theorem physicalField_continuous (T : ℝ≥0) : Continuous (physicalField T) := by
  unfold physicalField ComplexL2Isometry.combine
  have hr := ((ComplexL2Isometry.ofReal (ρ T)).continuous.comp (fieldEmbedding T).continuous).comp (realInput T).continuous
  have hi := ((ComplexL2Isometry.ofReal (ρ T)).continuous.comp (fieldEmbedding T).continuous).comp (imagInput T).continuous
  exact hr.add (hi.const_smul Complex.I)

private theorem unassociate_preserving (T : ℝ≥0) :
    MeasurePreserving (fun q : ℝ × Sample => ((q.1,q.2.1),q.2.2)) ((timeLaw T).prod μ) (ρ T) := by
  rw [ρ,timeMeasure,PredictableRealL2.horizonMeasure_eq_product]
  exact (measurePreserving_prodAssoc (timeLaw T) gaussianProduct gaussianProduct).symm

private theorem physicalField_actual (T : ℝ≥0) (u : ComplexInput T) :
    ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,physicalField T u ((r,w.1),w.2)=
      (fieldEmbedding T (realInput T u) ((r,w.1),w.2):ℂ)+
        Complex.I*(fieldEmbedding T (imagInput T u) ((r,w.1),w.2):ℂ) :=
  ae_ae_of_ae_prod ((unassociate_preserving T).quasiMeasurePreserving.ae
    (ComplexL2Isometry.combine_ae (ρ T) _ _))

/-- Strong native convergence plus pointwise disk derivative convergence identifies
its SAME physical stopped field. No uniform derivative estimate is assumed. -/
theorem derivative_input_limit (p : ℕ → Polynomial ℂ) (g : ℂ → ℂ)
    (R : ℝ) (hR : 0≤R) (T : ℝ≥0) (u : ComplexInput T)
    (hu : Tendsto (fun n => exitDerivativeInput (p n) R T) atTop (𝓝 u))
    (hg : ∀ z,‖z‖≤R → Tendsto (fun n => (p n).derivative.eval z) atTop (𝓝 (g z))) :
    ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,
      (fieldEmbedding T (realInput T u) ((r,w.1),w.2):ℂ)+
        Complex.I*(fieldEmbedding T (imagInput T u) ((r,w.1),w.2):ℂ)=
      {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator
        (fun w => g (StochasticCauchyBrownianRealization.value r.toNNReal w)) w := by
  have hl := (physicalField_continuous T).tendsto u |>.comp hu
  obtain ⟨k,hk,hn⟩ := (tendstoInMeasure_of_tendsto_Lp hl).exists_seq_tendsto_ae
  have hna := ae_ae_of_ae_prod ((unassociate_preserving T).quasiMeasurePreserving.ae hn)
  filter_upwards [hna,physicalField_actual T u,
    ae_all_iff.mpr (fun n => physicalField_actual T (exitDerivativeInput (p n) R T)),
    ae_all_iff.mpr (fun n => exitDerivativeInput_physical (p n) R hR T)] with r hn hu hnfield hnpoly
  filter_upwards [hn,hu,ae_all_iff.mpr hnfield,ae_all_iff.mpr hnpoly,exit_bounded_ae R hR r.toNNReal]
    with w hn hu hnfield hnpoly hb
  have he (n : ℕ) : physicalField T (exitDerivativeInput (p (k n)) R T) ((r,w.1),w.2)=
      {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator
        (fun w => (p (k n)).derivative.eval (StochasticCauchyBrownianRealization.value r.toNNReal w)) w :=
    (hnfield (k n)).trans (hnpoly (k n))
  have ht : Tendsto (fun n =>
      {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator
        (fun w => (p (k n)).derivative.eval (StochasticCauchyBrownianRealization.value r.toNNReal w)) w) atTop
      (𝓝 ({w : Sample | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator
        (fun w => g (StochasticCauchyBrownianRealization.value r.toNNReal w)) w)) := by
    by_cases hh : (r.toNNReal:WithTop ℝ≥0)≤exitTime R w
    · have hc : clippedClock r.toNNReal (exitTime R) w=r.toNNReal := by
        apply WithTop.coe_injective
        rw [clippedClock_coe,min_eq_right hh]
      rw [hc] at hb
      simpa only [Function.comp_def,Set.indicator,Set.mem_ofPred_eq,hh,ite_true] using
        (hg _ hb).comp hk.tendsto_atTop
    · simpa only [Set.indicator,Set.mem_ofPred_eq,hh,ite_false] using (tendsto_const_nhds (x := (0:ℂ)))
  simp only [Function.comp_def,he] at hn
  exact hu.symm.trans (tendsto_nhds_unique hn ht)


theorem derivative_eval (a z : ℂ) (n : ℕ) :
    (resolventPolynomial a (n+1)).derivative.eval z=
      a⁻¹^2 * ∑ j ∈ Finset.range n,((j:ℂ)+1)*(a⁻¹*z)^j := by
  rw [resolventPolynomial,Polynomial.derivative_mul,Polynomial.derivative_C,zero_mul,zero_add,
    Polynomial.derivative_sum,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_finsetSum,
    Finset.sum_range_succ']
  simp only [pow_zero,Polynomial.derivative_one,Polynomial.eval_zero,add_zero,
    Polynomial.derivative_pow_succ,Polynomial.derivative_mul,Polynomial.derivative_C,zero_mul,
    Polynomial.derivative_X,zero_add,mul_one,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem derivative_tendsto (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) (z : ℂ) (hz : ‖z‖≤R) :
    Tendsto (fun n => (resolventPolynomial a (n+1)).derivative.eval z) atTop (𝓝 ((a-z)⁻¹^2)) := by
  have hap : 0<‖a‖ := lt_of_le_of_lt hR ha
  have ha0 : a≠0 := norm_pos_iff.mp hap
  have haz : a-z≠0 := by
    intro he
    have heq : a=z := sub_eq_zero.mp he
    rw [heq] at ha
    exact (not_lt_of_ge hz) ha
  have hzz : ‖a⁻¹*z‖<1 := by
    calc
      ‖a⁻¹*z‖ = ‖z‖/‖a‖ := by rw [norm_mul,norm_inv];ring
      _ < 1 := (div_lt_one hap).mpr (lt_of_le_of_lt hz ha)
  have ht := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hzz).tendsto_sum_nat.const_mul (a⁻¹^2)
  have he : a⁻¹^2*(1/(1-a⁻¹*z)^2)=(a-z)⁻¹^2 := by field_simp
  simpa only [derivative_eval,Nat.choose_one_right,Nat.cast_add,Nat.cast_one,he] using ht

/-- ACTUAL local resolvent Ito identity with the SAME native input's physical
stopped derivative, strong input approximation and zero anti-channel. -/
theorem resolvent_ito (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) (T : ℝ≥0) :
    ∃ v : ComplexInput T,
      (channel T false (((Real.sqrt 2:ℝ):ℂ) • v) =ᵐ[μ] fun w =>
        (a-StochasticCauchyBrownianRealization.value (clippedClock T (exitTime R) w) w)⁻¹-a⁻¹) ∧
      (∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,
        (fieldEmbedding T (realInput T v) ((r,w.1),w.2):ℂ)+
          Complex.I*(fieldEmbedding T (imagInput T v) ((r,w.1),w.2):ℂ)=
        {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator
          (fun w => (a-StochasticCauchyBrownianRealization.value r.toNNReal w)⁻¹^2) w) ∧
      Tendsto (fun n => exitDerivativeInput (resolventPolynomial a (n+1)) R T) atTop (𝓝 v) ∧
      channelAdjoint T true (channel T false (((Real.sqrt 2:ℝ):ℂ) • v))=0 := by
  obtain ⟨u,hu,hn,hanti⟩ := resolvent_native a R hR ha T
  let α : ℂ := ((Real.sqrt 2:ℝ):ℂ)
  have hα : α≠0 := by
    change ((Real.sqrt 2:ℝ):ℂ)≠0
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  change Tendsto (fun n => α • exitDerivativeInput (resolventPolynomial a n) R T) atTop (𝓝 u) at hn
  let v : ComplexInput T := α⁻¹ • u
  have he : α • v=u := by
    dsimp only [v]
    rw [smul_smul,mul_inv_cancel₀ hα,one_smul]
  have hv : Tendsto (fun n => exitDerivativeInput (resolventPolynomial a n) R T) atTop (𝓝 v) := by
    simpa only [smul_smul,inv_mul_cancel₀ hα,one_smul] using hn.const_smul α⁻¹
  have hvshift : Tendsto (fun n => exitDerivativeInput (resolventPolynomial a (n+1)) R T) atTop (𝓝 v) := by
    simpa only [Function.comp_def] using hv.comp (tendsto_add_atTop_nat 1)
  refine ⟨v,?_,?_,hvshift,?_⟩
  · exact he ▸ hu
  · exact derivative_input_limit (fun n => resolventPolynomial a (n+1)) (fun z => (a-z)⁻¹^2)
      R hR T v hvshift (fun z hz => derivative_tendsto a R hR ha z hz)
  · exact he ▸ hanti

end OperatorDerivativeRewrite.Foundation.StochasticCauchyDiskDerivative
