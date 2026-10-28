import Foundation.SU2HomogeneousPlaquetteObstruction

/-! A homogeneous plaquette-exchange trial and its actual nonperturbative form
comparison. No eigenbranch, vacuum existence, or four-dimensional bridge is
postulated. The result concerns this bare trial, not all higher corrections. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2HomogeneousExchangeTrial
open QuaternionSU2Representation SU2WilsonConvolution SU2SevenLinkTransfer
open SU2SevenLinkVariational SU2SevenLinkOddTrial SU2SevenLinkParity
open SU2HomogeneousPlaquetteObstruction

/-- Actual joint-Haar reduction for the two adjacent plaquette half-traces.
It does not assert independence under a nonzero-temporal-coupling vacuum. -/
theorem joint_haar_integral (F : ℝ × ℝ → ℝ) (hF : Measurable F)
    (B : ℝ) (hb : ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → |F (x,y)| ≤ B) :
    (∫ s, F (first s,second s) ∂haar)=∫ P, ∫ Q, F (halfTrace P,halfTrace Q) ∂law ∂law := by
  change (∫ s, F (halfTrace (leftPath s*s.1),halfTrace (s.1⁻¹*rightPath s)) ∂haar)=_
  rw [haar_path_integral (fun L R U => F (halfTrace (L*U),halfTrace (U⁻¹*R)))
    (hF.comp (first_measurable.prodMk second_measurable)) B
    (fun L R U => hb _ _ (halfTrace_bound _) (halfTrace_bound _))]
  have hr (L U : SU2) :
      (∫ R, F (halfTrace (L*U),halfTrace (U⁻¹*R)) ∂law)=∫ Q, F (halfTrace (L*U),halfTrace Q) ∂law :=
    integral_mul_left_eq_self (fun Q => F (halfTrace (L*U),halfTrace Q)) U⁻¹
  simp_rw [hr]
  have hl (U : SU2) : (∫ L, ∫ Q, F (halfTrace (L*U),halfTrace Q) ∂law ∂law)=
      ∫ P, ∫ Q, F (halfTrace P,halfTrace Q) ∂law ∂law := by
    simp_rw [halfTrace_mul_comm _ U]
    exact integral_mul_left_eq_self (fun P => ∫ Q, F (halfTrace P,halfTrace Q) ∂law) U
  simp_rw [hl]
  simp

/-- Simultaneous sign reversal is a symmetry of the actual joint Haar law. -/
theorem joint_sign_integral (F : ℝ × ℝ → ℝ) (hF : Measurable F)
    (B : ℝ) (hb : ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → |F (x,y)| ≤ B) :
    (∫ s, F (-first s,-second s) ∂haar)=∫ s, F (first s,second s) ∂haar := by
  have hm : Measurable (fun p : ℝ × ℝ => F (-p.1,-p.2)) := hF.comp (by fun_prop)
  rw [joint_haar_integral _ hm B (fun x y hx hy => hb (-x) (-y) (by simpa using hx) (by simpa using hy)),
    joint_haar_integral F hF B hb]
  have hr (P : SU2) : (∫ Q, F (-halfTrace P,-halfTrace Q) ∂law)=∫ Q, F (-halfTrace P,halfTrace Q) ∂law := by
    have h := integral_mul_left_eq_self (μ := law) (fun Q => F (-halfTrace P,halfTrace Q)) SU2StapleExtremes.minusOne
    simpa only [SU2StrongCouplingCovariance.halfTrace_center_neg] using h
  simp_rw [hr]
  have h := integral_mul_left_eq_self (μ := law) (fun P => ∫ Q, F (halfTrace P,halfTrace Q) ∂law) SU2StapleExtremes.minusOne
  simpa only [SU2StrongCouplingCovariance.halfTrace_center_neg] using h

/-- Bare exchange-antisymmetric, gauge-invariant closed-loop observable. -/
def delta (s : State) : ℝ := second s-first s

theorem delta_measurable : Measurable delta := second_measurable.sub first_measurable

theorem delta_bound (s : State) : |delta s| ≤ 2 := by
  unfold delta
  exact (abs_sub _ _).trans (by linarith [second_bound s,first_bound s])

theorem delta_gauge (g : Fin 6 → SU2) (s : State) : delta (gaugeAction g s)=delta s := by
  unfold delta
  rw [second_gauge,first_gauge]

private theorem square_integrable : Integrable (fun s => delta s^2) haar := by
  apply Integrable.of_bound (delta_measurable.pow_const 2).aestronglyMeasurable 4
  filter_upwards with s
  rw [Real.norm_eq_abs,abs_pow]
  exact (pow_le_pow_left₀ (abs_nonneg _) (delta_bound s) 2).trans (by norm_num)

theorem delta_square : (∫ s, delta s^2 ∂haar)=(1/2:ℝ) := by
  have hX := BoundedExponentialTiltResponse.bounded_power_integrable haar first first_measurable first_bound 2
  have hY := BoundedExponentialTiltResponse.bounded_power_integrable haar second second_measurable second_bound 2
  have hXY : Integrable (fun s => second s*first s) haar := by
    apply Integrable.of_bound (second_measurable.mul first_measurable).aestronglyMeasurable 1
    filter_upwards with s
    change ‖second s*first s‖ ≤ 1
    rw [Real.norm_eq_abs,abs_mul]
    simpa using mul_le_mul (second_bound s) (first_bound s) (abs_nonneg _) (by norm_num)
  have hzero : (∫ s, second s*first s ∂haar)=0 := odd_even_orthogonal second first second_flip first_flip
  have he (s : State) : delta s^2=(second s^2+first s^2)-2*(second s*first s) := by unfold delta; ring
  simp_rw [he]
  have hsub := integral_sub (hY.add hX) (hXY.const_mul 2)
  have hadd := integral_add hY hX
  simp only [Pi.add_apply,Pi.sub_apply] at hsub hadd
  rw [hsub,hadd,integral_const_mul,haar_second_square,haar_first_second_moment,hzero]
  norm_num

theorem delta_eigen (β : ℝ) (s : State) : SU2SevenLinkTransfer.step β delta s=coefficient β^4*delta s := by
  have hX := step_integrable β first first_measurable 1 first_bound s
  have hY := step_integrable β second second_measurable 1 second_bound s
  unfold SU2SevenLinkTransfer.step delta
  rw [integral_sub hY hX]
  change SU2SevenLinkTransfer.step β second s-SU2SevenLinkTransfer.step β first s=_
  rw [step_second,step_first]
  ring

/-- Actual homogeneous spatial form, using the SAME seven-link kinetic transfer. -/
def form (β t : ℝ) (f g : State → ℝ) : ℝ := pairing β (fun s => weight t s*f s) (fun s => weight t s*g s)

theorem form_integral (β t : ℝ) (f g : State → ℝ) :
    form β t f g=∫ s, f s*homogeneousStep β t g s ∂haar := by
  unfold form pairing homogeneousStep
  apply integral_congr_ae
  filter_upwards with s
  ring

def unweight (t : ℝ) (f : State → ℝ) (s : State) : ℝ := Real.exp (-t*potential s)*f s

theorem weight_unweight (t : ℝ) (f : State → ℝ) (s : State) : weight t s*unweight t f s=f s := by
  unfold weight unweight
  rw [← mul_assoc,← Real.exp_add,show t*potential s+ -t*potential s=0 by ring,Real.exp_zero,one_mul]

theorem form_unweight (β t : ℝ) (f g : State → ℝ) : form β t (unweight t f) (unweight t g)=pairing β f g := by
  unfold form
  simp_rw [weight_unweight]

/-- Exact, nonperturbative numerator for the actual homogeneous spatial trial. -/
theorem delta_numerator (β t : ℝ) : form β t (unweight t delta) (unweight t delta)=coefficient β^4/2 := by
  rw [form_unweight]
  unfold pairing
  simp_rw [delta_eigen]
  have he (s : State) : delta s*(coefficient β^4*delta s)=coefficient β^4*delta s^2 := by ring
  simp_rw [he]
  rw [integral_const_mul,delta_square]
  ring

/-- The actual inverse-weighted homogeneous norm, not a formal Taylor coefficient. -/
def denominator (t : ℝ) : ℝ := ∫ s, Real.exp (-t*(first s+second s))*delta s^2 ∂haar

theorem denominator_norm (t : ℝ) : (∫ s, (unweight t delta s)^2 ∂haar)=denominator t := by
  unfold denominator unweight
  apply integral_congr_ae
  filter_upwards with s
  rw [mul_pow,pow_two (Real.exp _),← Real.exp_add]
  unfold potential
  congr 2
  ring

private theorem density_square_integrable (t : ℝ) :
    Integrable (fun s => Real.exp (-t*(first s+second s))*delta s^2) haar := by
  have he := BoundedExponentialTiltResponse.exponential_integrable haar potential potential_measurable potential_bound (-2*t)
  have h := he.bdd_mul (delta_measurable.pow_const 2).aestronglyMeasurable (c := 4) (by
    filter_upwards with s
    rw [Real.norm_eq_abs,abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (delta_bound s) 2).trans (by norm_num))
  convert h using 1
  funext s
  have heq : -t*(first s+second s)= -2*t*potential s := by unfold potential; ring
  rw [heq,mul_comm]

private theorem exponential_sum_bound (t x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    Real.exp (-t*(x+y)) ≤ Real.exp (2*|t|) := by
  apply Real.exp_le_exp.mpr
  have hxy : |x+y| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  have hp : |-t*(x+y)| ≤ 2*|t| := by
    rw [abs_mul,abs_neg]
    nlinarith [mul_le_mul_of_nonneg_left hxy (abs_nonneg t)]
  exact (le_abs_self _).trans hp

/-- Exact evenness in spatial tilt of the actual trial norm. -/
theorem denominator_even (t : ℝ) : denominator (-t)=denominator t := by
  let F := fun p : ℝ × ℝ => Real.exp (-t*(p.1+p.2))*(p.2-p.1)^2
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hb (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |F (x,y)| ≤ Real.exp (2*|t|)*4 := by
    dsimp [F]
    rw [abs_mul,abs_of_pos (Real.exp_pos _),abs_pow]
    have hd : |y-x| ≤ 2 := (abs_sub _ _).trans (by linarith)
    exact mul_le_mul (exponential_sum_bound t x y hx hy)
      ((pow_le_pow_left₀ (abs_nonneg _) hd 2).trans (by norm_num)) (sq_nonneg _) (Real.exp_pos _).le
  have h := joint_sign_integral F hF _ hb
  have he (s : State) : F (-first s,-second s)=Real.exp (-(-t)*(first s+second s))*delta s^2 := by
    dsimp [F]
    rw [show -t*(-first s+-second s)= -(-t)*(first s+second s) by ring]
    unfold delta
    ring
  simp_rw [he] at h
  exact h

/-- Actual ALL-TILT norm lower bound. It uses joint Haar sign symmetry and
exp(z)+exp(-z)>=2, not a second-order or formal eigenbranch expansion. -/
theorem denominator_lower (t : ℝ) : (1/2:ℝ) ≤ denominator t := by
  have hm := density_square_integrable t
  have hp : Integrable (fun s => Real.exp (t*(first s+second s))*delta s^2) haar := by
    simpa only [neg_neg] using density_square_integrable (-t)
  have hpoint (s : State) : 2*delta s^2 ≤ Real.exp (-t*(first s+second s))*delta s^2+
      Real.exp (t*(first s+second s))*delta s^2 := by
    have h1 := Real.add_one_le_exp (-t*(first s+second s))
    have h2 := Real.add_one_le_exp (t*(first s+second s))
    have hh : 0 ≤ Real.exp (-t*(first s+second s))+Real.exp (t*(first s+second s))-2 := by linarith
    nlinarith [mul_nonneg hh (sq_nonneg (delta s))]
  have hi := integral_mono (square_integrable.const_mul 2) (hm.add hp) hpoint
  have hadd := integral_add hm hp
  rw [integral_const_mul,delta_square] at hi
  change 2*(1/2:ℝ) ≤ ∫ s, Real.exp (-t*(first s+second s))*delta s^2+Real.exp (t*(first s+second s))*delta s^2 ∂haar at hi
  rw [hadd] at hi
  have he : (∫ s, Real.exp (t*(first s+second s))*delta s^2 ∂haar)=denominator (-t) := by
    simp only [denominator,neg_neg]
  rw [he] at hi
  change 2*(1/2:ℝ) ≤ denominator t+denominator (-t) at hi
  rw [denominator_even] at hi
  linarith

theorem denominator_positive (t : ℝ) : 0 < denominator t := lt_of_lt_of_le (by norm_num) (denominator_lower t)

def quotient (β t : ℝ) : ℝ := form β t (unweight t delta) (unweight t delta)/denominator t

/-- A rigorous obstruction to the BARE exchange-trial inflation route, for
EVERY actual Wilson parameter and EVERY spatial tilt. No vacuum is assumed. -/
theorem quotient_le_kinetic (β t : ℝ) : quotient β t ≤ coefficient β^4 := by
  unfold quotient
  rw [delta_numerator]
  apply (div_le_iff₀ (denominator_positive t)).mpr
  have ha : 0 ≤ coefficient β^4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (denominator_lower t) ha]

/-- Conditional normalized version. The lower bound lam>=1 is explicit;
this theorem does not construct a spatial eigenfunction or stationary law. -/
theorem normalized_quotient_le_kinetic (β t lam : ℝ) (hlam : 1 ≤ lam) : quotient β t/lam ≤ coefficient β^4 := by
  apply (div_le_iff₀ (by linarith : 0 < lam)).mpr
  have ha : 0 ≤ coefficient β^4 := by positivity
  exact (quotient_le_kinetic β t).trans (by nlinarith [mul_le_mul_of_nonneg_left hlam ha])

/-- Exchange is an exact symmetry of the joint Haar plaquette law. -/
theorem joint_swap_integral (F : ℝ × ℝ → ℝ) (hF : Measurable F)
    (B : ℝ) (hb : ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → |F (x,y)| ≤ B) :
    (∫ s, F (second s,first s) ∂haar)=∫ s, F (first s,second s) ∂haar := by
  have hm : Measurable (fun p : ℝ × ℝ => F (p.2,p.1)) := hF.comp (by fun_prop)
  rw [joint_haar_integral _ hm B (fun x y hx hy => hb y x hy hx),joint_haar_integral F hF B hb]
  have hi : Integrable (fun p : SU2 × SU2 => F (halfTrace p.1,halfTrace p.2)) (law.prod law) := by
    apply Integrable.of_bound (hF.comp ((halfTrace_measurable.comp measurable_fst).prodMk
      (halfTrace_measurable.comp measurable_snd))).aestronglyMeasurable B
    filter_upwards with p
    change ‖F (halfTrace p.1,halfTrace p.2)‖ ≤ B
    simpa only [Real.norm_eq_abs] using hb _ _ (halfTrace_bound _) (halfTrace_bound _)
  exact (integral_integral_swap hi).symm

/-- The corrected bare exchange observable IS centered under the actual
homogeneous reset law, in contrast with the transplanted one-weight trial. -/
theorem delta_reset_centered (t : ℝ) : (∫ s, delta s ∂stationary t)=0 := by
  let F := fun p : ℝ × ℝ => (p.2-p.1)*Real.exp (t*(p.1+p.2))
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hb (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |F (x,y)| ≤ 2*Real.exp (2*|t|) := by
    dsimp [F]
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    have hd : |y-x| ≤ 2 := (abs_sub _ _).trans (by linarith)
    have he := exponential_sum_bound (-t) x y hx hy
    simp only [neg_neg,abs_neg] at he
    exact mul_le_mul hd he (Real.exp_pos _).le (by norm_num)
  have hs := joint_swap_integral F hF _ hb
  have he (s : State) : F (second s,first s)= -(delta s*Real.exp (t*(first s+second s))) := by
    dsimp [F,delta]
    rw [add_comm (second s) (first s)]
    ring
  simp_rw [he] at hs
  rw [integral_neg] at hs
  change -(∫ s, delta s*Real.exp (t*(first s+second s)) ∂haar)=∫ s, delta s*Real.exp (t*(first s+second s)) ∂haar at hs
  have hz : (∫ s, delta s*Real.exp (t*(first s+second s)) ∂haar)=0 := by linarith
  rw [stationary,BoundedExponentialTiltResponse.tilted_integral haar potential delta potential_measurable potential_bound]
  unfold BoundedExponentialTiltResponse.expectation BoundedExponentialTiltResponse.weighted
  have hp (s : State) : (2*t)*potential s=t*(first s+second s) := by unfold potential; ring
  simp_rw [hp]
  rw [hz,zero_div]

theorem trial_measurable (t : ℝ) : Measurable (unweight t delta) :=
  ((measurable_const.mul potential_measurable).exp).mul delta_measurable

theorem trial_bound (t : ℝ) (s : State) : |unweight t delta s| ≤ Real.exp |t| * 2 := by
  unfold unweight
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  have hphase : -t*potential s ≤ |t| := calc
    _ ≤ |-t*potential s| := le_abs_self _
    _ = |t| * |potential s| := by rw [abs_mul,abs_neg]
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (potential_bound s) (abs_nonneg t)
    _ = |t| := mul_one _
  exact mul_le_mul (Real.exp_le_exp.mpr hphase) (delta_bound s) (abs_nonneg _) (Real.exp_pos _).le

theorem trial_memLp (t : ℝ) : MemLp (unweight t delta) 2 haar :=
  MemLp.of_bound (trial_measurable t).aestronglyMeasurable _ (ae_of_all _ (trial_bound t))

/-- The actual inverse-ground observable of this Rayleigh trial is centered in
the homogeneous reset model too, not just the untransformed delta observable. -/
theorem inverse_ground_reset_centered (t : ℝ) :
    (∫ s, unweight t delta s/weight t s ∂stationary t)=0 := by
  have hmean : (∫ s, delta s ∂haar)=0 := by
    have h := delta_reset_centered 0
    simpa [stationary,BoundedExponentialTiltResponse.tiltedMeasure,
      BoundedExponentialTiltResponse.density,BoundedExponentialTiltResponse.partition_zero] using h
  rw [stationary,BoundedExponentialTiltResponse.tilted_integral haar potential _ potential_measurable potential_bound]
  unfold BoundedExponentialTiltResponse.expectation BoundedExponentialTiltResponse.weighted
  have he (s : State) : (unweight t delta s/weight t s)*Real.exp ((2*t)*potential s)=delta s := by
    unfold unweight weight
    rw [show -t*potential s= -(t*potential s) by ring,Real.exp_neg,
      show (2*t)*potential s=t*potential s+t*potential s by ring,Real.exp_add]
    field_simp [Real.exp_ne_zero (t*potential s)]
  simp_rw [he]
  rw [hmean,zero_div]

end OperatorDerivativeRewrite.Foundation.SU2HomogeneousExchangeTrial
