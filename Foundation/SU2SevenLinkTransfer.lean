import Foundation.SU2WilsonGroundCertificate

/-! One actual seven-link SU2 temporal transfer for two adjacent plaquettes.
The shared edge is updated once. No stationary vacuum, normalized spectral
comparison or four-dimensional volume-uniform bound is assumed. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel
open SU2SharedPlaquetteProjection SU2WilsonGroundCertificate

private instance su2_secondCountable : SecondCountableTopology SU2 := by
  letI : SecondCountableTopology (Quaternion ℝ) :=
    Quaternion.linearIsometryEquivTuple.toHomeomorph.secondCountableTopology
  exact homeomorph.symm.secondCountableTopology

/-- Coordinates are (shared U,A,B,C,D,E,F); every physical link occurs once. -/
abbrev State := SU2 × SU2 × SU2 × SU2 × SU2 × SU2 × SU2

private instance state_secondCountable : SecondCountableTopology State := by infer_instance
private instance state_borel : BorelSpace State := by infer_instance

def edgeLaw (ν : Measure SU2) : Measure State :=
  ν.prod (ν.prod (ν.prod (ν.prod (ν.prod (ν.prod ν)))))

theorem edgeLaw_probability (ν : Measure SU2) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (edgeLaw ν) := by unfold edgeLaw; infer_instance

def noise (β : ℝ) : Measure State := edgeLaw (increment β)
def haar : Measure State := edgeLaw law

theorem noise_probability (β : ℝ) : IsProbabilityMeasure (noise β) := by
  letI := increment_probability β
  exact edgeLaw_probability _

instance haar_probability : IsProbabilityMeasure haar := edgeLaw_probability _

def leftPath (s : State) : SU2 := s.2.1*s.2.2.1*s.2.2.2.1
def rightPath (s : State) : SU2 := s.2.2.2.2.1*s.2.2.2.2.2.1*s.2.2.2.2.2.2

def first (s : State) : ℝ := halfTrace (leftPath s*s.1)
def second (s : State) : ℝ := halfTrace (s.1⁻¹*rightPath s)
def meanChannel (s : State) : ℝ := sharedMean (leftPath s) (rightPath s)
def residual (s : State) : ℝ := sharedResidual (leftPath s) (rightPath s) s.1

def step (β : ℝ) (f : State → ℝ) (s : State) : ℝ := ∫ v, f (s*v) ∂noise β

theorem first_measurable : Measurable first :=
  halfTrace_measurable.comp (by unfold leftPath; fun_prop)
theorem second_measurable : Measurable second :=
  halfTrace_measurable.comp (by unfold rightPath; fun_prop)
theorem meanChannel_measurable : Measurable meanChannel := by
  unfold meanChannel sharedMean
  exact (halfTrace_measurable.comp (by unfold leftPath rightPath; fun_prop)).div_const 4

theorem residual_measurable : Measurable residual := by
  change Measurable (fun s => first s*second s-meanChannel s)
  exact (first_measurable.mul second_measurable).sub meanChannel_measurable

theorem first_bound (s : State) : |first s| ≤ 1 := halfTrace_bound _
theorem second_bound (s : State) : |second s| ≤ 1 := halfTrace_bound _
theorem meanChannel_bound (s : State) : |meanChannel s| ≤ 1 := sharedMean_bound _ _
theorem residual_bound (s : State) : |residual s| ≤ 2 := by
  change |first s*second s-meanChannel s| ≤ 2
  have hp : |first s*second s| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul (first_bound s) (second_bound s) (abs_nonneg _) (by norm_num)
  have h := norm_sub_le (first s*second s) (meanChannel s)
  simp only [Real.norm_eq_abs] at h
  linarith [meanChannel_bound s]

theorem step_integrable (β : ℝ) (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s, |f s| ≤ B) (s : State) : Integrable (fun v => f (s*v)) (noise β) := by
  letI := noise_probability β
  apply Integrable.of_bound (hf.comp ((continuous_const_mul s).measurable)).aestronglyMeasurable B
  filter_upwards with v
  simpa only [Real.norm_eq_abs,Function.comp_apply] using hb (s*v)

private theorem bounded_product_integral {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X × Y → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ z, |f z| ≤ B) :
    (∫ z, f z ∂μ.prod ν)=∫ x, ∫ y, f (x,y) ∂ν ∂μ := by
  apply integral_prod
  apply Integrable.of_bound hf.aestronglyMeasurable B
  filter_upwards with z
  simpa only [Real.norm_eq_abs] using hb z

/-- Bounded measurable Fubini on exactly the seven-link product law. -/
theorem integral_seven (ν : Measure SU2) [IsProbabilityMeasure ν]
    (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ s, |f s| ≤ B) :
    (∫ s, f s ∂edgeLaw ν)=
      ∫ U, ∫ A, ∫ B, ∫ C, ∫ D, ∫ E, ∫ F, f (U,A,B,C,D,E,F)
        ∂ν ∂ν ∂ν ∂ν ∂ν ∂ν ∂ν := by
  unfold edgeLaw
  rw [bounded_product_integral _ _ f hf B hb]
  congr 1
  funext U
  rw [bounded_product_integral _ _ (fun p => f (U,p)) (hf.comp (by fun_prop)) B (fun p => hb (U,p))]
  congr 1
  funext A
  rw [bounded_product_integral _ _ (fun p => f (U,A,p)) (hf.comp (by fun_prop)) B (fun p => hb (U,A,p))]
  congr 1
  funext B'
  rw [bounded_product_integral _ _ (fun p => f (U,A,B',p)) (hf.comp (by fun_prop)) B (fun p => hb (U,A,B',p))]
  congr 1
  funext C
  rw [bounded_product_integral _ _ (fun p => f (U,A,B',C,p)) (hf.comp (by fun_prop)) B (fun p => hb (U,A,B',C,p))]
  congr 1
  funext D
  rw [bounded_product_integral _ _ (fun p => f (U,A,B',C,D,p)) (hf.comp (by fun_prop)) B (fun p => hb (U,A,B',C,D,p))]

/-- The previously verified shared channel is now an identity for THIS full product operator. -/
theorem step_residual (β : ℝ) (s : State) :
    step β residual s=coefficient β^6*quadraticCoefficient β*residual s := by
  letI := increment_probability β
  unfold step noise
  rw [integral_seven _ (fun v => residual (s*v)) (residual_measurable.comp ((continuous_const_mul s).measurable)) 2 (fun v => residual_bound (s*v))]
  have h := twoPlaquette_residual_average β s.2.1 s.2.2.1 s.2.2.2.1
    s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2 s.1
  simpa only [sharedWordAverage,residualWords,rightWords,residual,leftPath,rightPath,
    Prod.fst_mul,Prod.snd_mul,one_mul,mul_assoc] using h

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel
open SU2SharedPlaquetteProjection SU2WilsonGroundCertificate

private theorem mean_six_average (β : ℝ) (A B C D E F : SU2) :
    (∫ a, ∫ b, ∫ c, ∫ d, ∫ e, ∫ f,
      halfTrace ((A*a)*(B*b)*(C*c)*((D*d)*(E*e)*(F*f)))
      ∂increment β ∂increment β ∂increment β ∂increment β ∂increment β ∂increment β)/4=
      coefficient β^6*(halfTrace ((A*B*C)*(D*E*F))/4) := by
  have h := outerRectangle_average β [A,B,C] [D,E,F]
  simp only [List.cons_append,List.nil_append,List.length_cons,List.length_nil,
    Nat.reduceAdd,List.prod_cons,List.prod_nil] at h
  dsimp only [wordAverage] at h
  simpa only [one_mul,mul_one,sharedMean,mul_assoc] using h

theorem step_meanChannel (β : ℝ) (s : State) :
    step β meanChannel s=coefficient β^6*meanChannel s := by
  letI := increment_probability β
  unfold step noise
  rw [integral_seven _ (fun v => meanChannel (s*v)) (meanChannel_measurable.comp ((continuous_const_mul s).measurable))
    1 (fun v => meanChannel_bound (s*v))]
  simp only [meanChannel,sharedMean,leftPath,rightPath,Prod.fst_mul,Prod.snd_mul]
  simp only [integral_const,probReal_univ,one_smul]
  simp_rw [integral_div]
  exact mean_six_average β s.2.1 s.2.2.1 s.2.2.2.1
    s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2

private theorem quadratic_sandwich (β : ℝ) (L R : SU2) :
    (∫ V, centeredSquare (L*V*R) ∂increment β)=quadraticCoefficient β*centeredSquare (L*R) := by
  have he (V : SU2) : centeredSquare (L*V*R)=centeredSquare ((R*L)*V) := by
    unfold centeredSquare
    rw [halfTrace_mul_comm (L*V) R]
    simp only [mul_assoc]
  simp_rw [he]
  change SU2WilsonConvolution.step β centeredSquare (R*L)=_
  rw [centeredSquare_step]
  unfold centeredSquare
  rw [halfTrace_mul_comm R L]

/-- Centered quadratic holonomy word with independent increments at each listed edge. -/
def quadraticWords (β : ℝ) : List SU2 → SU2 → ℝ
  | [], C => centeredSquare C
  | A::as, C => ∫ V, quadraticWords β as (C*A*V) ∂increment β

theorem quadraticWords_exact (β : ℝ) (as : List SU2) (C : SU2) :
    quadraticWords β as C=quadraticCoefficient β^as.length*centeredSquare (C*as.prod) := by
  induction as generalizing C with
  | nil => simp [quadraticWords]
  | cons A as ih =>
    simp only [quadraticWords,ih,integral_const_mul,List.length_cons,List.prod_cons]
    rw [quadratic_sandwich,pow_succ]
    simp only [mul_assoc]

private theorem first_cyclic (s : State) (U A B C D E F : SU2) :
    first (s*(U,A,B,C,D,E,F))=
      halfTrace ((s.1*U)*(s.2.1*A)*(s.2.2.1*B)*(s.2.2.2.1*C)) := by
  change halfTrace (((s.2.1*A)*(s.2.2.1*B)*(s.2.2.2.1*C))*(s.1*U))=_
  rw [halfTrace_mul_comm]
  simp only [mul_assoc]

theorem step_first (β : ℝ) (s : State) : step β first s=coefficient β^4*first s := by
  letI := increment_probability β
  unfold step noise
  rw [integral_seven _ (fun v => first (s*v)) (first_measurable.comp ((continuous_const_mul s).measurable))
    1 (fun v => first_bound (s*v))]
  simp_rw [first_cyclic]
  simp only [integral_const,probReal_univ,one_smul]
  have hprivate (U : SU2) :
      (∫ A, ∫ B, ∫ C, halfTrace ((s.1*U)*(s.2.1*A)*(s.2.2.1*B)*(s.2.2.2.1*C))
        ∂increment β ∂increment β ∂increment β)=
      coefficient β^3*halfTrace ((s.1*U)*(s.2.1*s.2.2.1*s.2.2.2.1)) := by
    simpa only [wordAverage,List.length_cons,List.length_nil,List.prod_cons,List.prod_nil,
      Nat.reduceAdd,mul_one,mul_assoc] using wordAverage_exact β [s.2.1,s.2.2.1,s.2.2.2.1] (s.1*U)
  simp_rw [hprivate]
  rw [integral_const_mul,trace_sandwich]
  unfold first leftPath
  rw [halfTrace_mul_comm]
  ring

theorem step_first_centered_square (β : ℝ) (s : State) :
    step β (fun r => first r^2-1/4) s=quadraticCoefficient β^4*(first s^2-1/4) := by
  letI := increment_probability β
  have hm : Measurable (fun r : State => first r^2-1/4) := first_measurable.pow_const 2 |>.sub measurable_const
  have hb (r : State) : |first r^2-1/4| ≤ 2 := by
    have hx := (sq_le_one_iff_abs_le_one (first r)).mpr (first_bound r)
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (first r)]
  unfold step noise
  rw [integral_seven _ (fun v => first (s*v)^2-1/4) (hm.comp ((continuous_const_mul s).measurable)) 2 (fun v => hb (s*v))]
  simp_rw [first_cyclic]
  simp only [integral_const,probReal_univ,one_smul]
  have hprivate (U : SU2) :
      (∫ A, ∫ B, ∫ C, (halfTrace ((s.1*U)*(s.2.1*A)*(s.2.2.1*B)*(s.2.2.2.1*C)))^2-1/4
        ∂increment β ∂increment β ∂increment β)=
      quadraticCoefficient β^3*centeredSquare ((s.1*U)*(s.2.1*s.2.2.1*s.2.2.2.1)) := by
    simpa only [quadraticWords,centeredSquare,List.length_cons,List.length_nil,List.prod_cons,List.prod_nil,
      Nat.reduceAdd,mul_one,mul_assoc] using quadraticWords_exact β [s.2.1,s.2.2.1,s.2.2.2.1] (s.1*U)
  simp_rw [hprivate]
  rw [integral_const_mul,quadratic_sandwich]
  unfold first leftPath centeredSquare
  rw [halfTrace_mul_comm]
  ring

theorem step_first_square (β : ℝ) (s : State) :
    step β (fun r => first r^2) s=1/4+quadraticCoefficient β^4*(first s^2-1/4) := by
  letI := noise_probability β
  have hi := step_integrable β (fun r => first r^2) (first_measurable.pow_const 2) 1 (fun r => by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg (first r)) (first_bound r) 2) s
  have h := step_first_centered_square β s
  unfold step at h ⊢
  rw [integral_sub hi (integrable_const _)] at h
  norm_num at h
  linarith

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel
open SU2WilsonGroundCertificate

/-- Literal plaquette half weights sandwich the SAME seven-link temporal operator. -/
def spatialStep (β t : ℝ) (f : State → ℝ) (s : State) : ℝ :=
  Real.exp (t*first s/2)*step β (fun r => Real.exp (t*first r/2)*f r) s

def trialVacuum (β t : ℝ) (s : State) : ℝ :=
  Real.exp (t*first s/2)*trial (linearCoefficient (coefficient β^4))
    (quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)) t (first s)

theorem trialVacuum_positive (β t : ℝ)
    (hsmall : |linearCoefficient (coefficient β^4)| * |t|+
      |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)| * |t|^2 ≤ 1/2)
    (s : State) : 0 < trialVacuum β t s := by
  exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le (by norm_num)
    (trial_positive _ _ _ _ (first_bound s) hsmall))

/-- A positive supersolution on the actual seven-link operator, with exact domains
and no vacuum existence or analytic perturbation premise. -/
theorem spatialStep_trialVacuum_supersolution (β t : ℝ) (ht : |t| ≤ 1)
    (hsmall : |linearCoefficient (coefficient β^4)| * |t|+
      |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)| * |t|^2 ≤ 1/2)
    (s : State) :
    spatialStep β t (trialVacuum β t) s ≤
      (1+vacuumSecond (coefficient β^4)*t^2+
        2*eigenErrorConstant (coefficient β^4) (quadraticCoefficient β^4)*|t|^3)*trialVacuum β t s := by
  letI := noise_probability β
  have h := exponential_trial_supersolution (noise β) (coefficient β^4)
    (quadraticCoefficient β^4) t (first s) (kinetic_power_ne_one β 4 (by decide)).1
    (kinetic_power_ne_one β 4 (by decide)).2 ht (first_bound s) hsmall
    (fun v => first (s*v)) (first_measurable.comp ((continuous_const_mul s).measurable))
    (fun v => first_bound (s*v)) (step_first β s) (step_first_square β s)
  have he (r : State) : Real.exp (t*first r/2)*trialVacuum β t r=
      Real.exp (t*first r)*trial (linearCoefficient (coefficient β^4))
        (quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)) t (first r) := by
    unfold trialVacuum
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  unfold spatialStep step
  simp_rw [he]
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (t*first s/2)).le
  simpa only [trialVacuum,mul_left_comm] using hm

theorem spatialStep_trialVacuum_integrable (β t : ℝ) (ht : |t| ≤ 1) (s : State) :
    Integrable (fun v => Real.exp (t*first (s*v)/2)*trialVacuum β t (s*v)) (noise β) := by
  letI := noise_probability β
  have he (r : State) : Real.exp (t*first r/2)*trialVacuum β t r=
      Real.exp (t*first r)*trial (linearCoefficient (coefficient β^4))
        (quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)) t (first r) := by
    unfold trialVacuum
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  have hm : Measurable (fun v : State => trial (linearCoefficient (coefficient β^4))
      (quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)) t (first (s*v))) := by
    unfold trial
    have hY := first_measurable.comp ((continuous_const_mul s).measurable)
    exact (measurable_const.add (measurable_const.mul hY)).add
      (measurable_const.mul ((hY.pow_const 2).sub measurable_const))
  have hdom (v : State) : |trial (linearCoefficient (coefficient β^4))
      (quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)) t (first (s*v))| ≤
      1+|linearCoefficient (coefficient β^4)|+
        |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)| :=
    trial_bound _ _ _ _ ht (first_bound (s*v))
  apply Integrable.of_bound (((measurable_const.mul
    (first_measurable.comp ((continuous_const_mul s).measurable))).exp.mul hm).aestronglyMeasurable)
    (Real.exp 1*(1+|linearCoefficient (coefficient β^4)|+
      |quadraticTrialCoefficient (coefficient β^4) (quadraticCoefficient β^4)|))
  filter_upwards with v
  change ‖Real.exp (t*first (s*v))*trial _ _ t (first (s*v))‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  have hx : t*first (s*v) ≤ 1 := calc
    _ ≤ |t*first (s*v)| := le_abs_self _
    _ = |t| * |first (s*v)| := abs_mul _ _
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (first_bound (s*v)) (abs_nonneg t)
    _ ≤ 1 := by simpa using ht
  exact mul_le_mul (Real.exp_le_exp.mpr hx) (hdom v) (abs_nonneg _) (Real.exp_pos _).le

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel
open SU2SharedPlaquetteProjection

private theorem three_haar (f : SU2 → ℝ) :
    (∫ A, ∫ B, ∫ C, f (A*B*C) ∂law ∂law ∂law)=∫ L, f L ∂law := by
  have he (A B : SU2) : (∫ C, f (A*B*C) ∂law)=∫ L, f L ∂law :=
    integral_mul_left_eq_self f (A*B)
  simp_rw [he]
  simp

/-- Actual product-Haar integration reduces the two private paths independently;
this is not gauge fixing or a boundary-conditioned probability assumption. -/
theorem haar_path_integral (F : SU2 → SU2 → SU2 → ℝ)
    (hF : Measurable (fun s : State => F (leftPath s) (rightPath s) s.1))
    (B : ℝ) (hb : ∀ L R U, |F L R U| ≤ B) :
    (∫ s, F (leftPath s) (rightPath s) s.1 ∂haar)=
      ∫ U, ∫ L, ∫ R, F L R U ∂law ∂law ∂law := by
  unfold haar
  rw [integral_seven _ _ hF B (fun s => hb _ _ _)]
  simp only [leftPath,rightPath]
  have hr (U A B C : SU2) :
      (∫ D, ∫ E, ∫ F', F (A*B*C) (D*E*F') U ∂law ∂law ∂law)=
      ∫ R, F (A*B*C) R U ∂law := three_haar (fun R => F (A*B*C) R U)
  simp_rw [hr]
  have hl (U : SU2) :
      (∫ A, ∫ B, ∫ C, (∫ R, F (A*B*C) R U ∂law) ∂law ∂law ∂law)=
      ∫ L, ∫ R, F L R U ∂law ∂law := three_haar (fun L => ∫ R, F L R U ∂law)
  simp_rw [hl]

theorem haar_residual_second_moment : (∫ s, residual s^2 ∂haar)=(3/64:ℝ) := by
  have hm : Measurable (fun s : State => residual s^2) := residual_measurable.pow_const 2
  have hb (L R U : SU2) : |sharedResidual L R U^2| ≤ 4 := by
    have h : |sharedResidual L R U| ≤ 2 := by
      have ht := norm_sub_le (sharedProduct L R U) (sharedMean L R)
      simp only [Real.norm_eq_abs] at ht
      change |sharedProduct L R U-sharedMean L R| ≤ 2
      linarith [sharedProduct_bound L R U,sharedMean_bound L R]
    rw [abs_pow]
    simpa only [show (2:ℝ)^2=4 by norm_num] using pow_le_pow_left₀ (abs_nonneg _) h 2
  change (∫ s, sharedResidual (leftPath s) (rightPath s) s.1^2 ∂haar)=_
  rw [haar_path_integral (fun L R U => sharedResidual L R U^2) hm 4 hb]
  simp_rw [fun U => (shared_projection_second_moments U).2.2]
  simp

theorem haar_mean_second_moment : (∫ s, meanChannel s^2 ∂haar)=(1/64:ℝ) := by
  have hm : Measurable (fun s : State => meanChannel s^2) := meanChannel_measurable.pow_const 2
  have hb (L R U : SU2) : |sharedMean L R^2| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) (sharedMean_bound L R) 2
  change (∫ s, sharedMean (leftPath s) (rightPath s)^2 ∂haar)=_
  rw [haar_path_integral (fun L R U => sharedMean L R^2) hm 1 hb]
  simpa only [integral_const,probReal_univ,one_smul] using
    (shared_projection_second_moments (1:SU2)).2.1

theorem haar_first_second_moment : (∫ s, first s^2 ∂haar)=(1/4:ℝ) := by
  have hm : Measurable (fun s : State => first s^2) := first_measurable.pow_const 2
  have hb (L R U : SU2) : |halfTrace (L*U)^2| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) (halfTrace_bound (L*U)) 2
  change (∫ s, halfTrace (leftPath s*s.1)^2 ∂haar)=_
  rw [haar_path_integral (fun L R U => halfTrace (L*U)^2) hm 1 hb]
  simp only [integral_const,probReal_univ,one_smul]
  simp_rw [trace_square_right_mean]
  simp

theorem residual_memLp : MemLp residual 2 haar := by
  apply MemLp.of_bound residual_measurable.aestronglyMeasurable 2
  filter_upwards with s
  simpa only [Real.norm_eq_abs] using residual_bound s

theorem meanChannel_memLp : MemLp meanChannel 2 haar := by
  apply MemLp.of_bound meanChannel_measurable.aestronglyMeasurable 1
  filter_upwards with s
  simpa only [Real.norm_eq_abs] using meanChannel_bound s

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer
open QuaternionSU2Representation SU2WilsonConvolution SU2QuadraticWilsonChannel
open SU2SharedPlaquetteProjection SU2WilsonGroundCertificate

theorem step_second (β : ℝ) (s : State) : step β second s=coefficient β^4*second s := by
  letI := increment_probability β
  unfold step noise
  rw [integral_seven _ (fun v => second (s*v))
    (second_measurable.comp ((continuous_const_mul s).measurable)) 1 (fun v => second_bound (s*v))]
  simp only [second,rightPath,Prod.fst_mul,Prod.snd_mul]
  simp only [integral_const,probReal_univ,one_smul]
  have hp (U : SU2) :
      (∫ D, ∫ E, ∫ F, halfTrace ((s.1*U)⁻¹*((s.2.2.2.2.1*D)*(s.2.2.2.2.2.1*E)*(s.2.2.2.2.2.2*F)))
        ∂increment β ∂increment β ∂increment β)=
      coefficient β^3*halfTrace ((s.1*U)⁻¹*rightPath s) := by
    simpa only [wordAverage,rightPath,List.length_cons,List.length_nil,List.prod_cons,List.prod_nil,
      Nat.reduceAdd,mul_one,mul_assoc] using wordAverage_exact β
      [s.2.2.2.2.1,s.2.2.2.2.2.1,s.2.2.2.2.2.2] (s.1*U)⁻¹
  simp_rw [hp]
  rw [integral_const_mul]
  have he (U : SU2) : halfTrace ((s.1*U)⁻¹*rightPath s)=halfTrace ((rightPath s)⁻¹*s.1*U) := by
    rw [← halfTrace_inv ((s.1*U)⁻¹*rightPath s)]
    simp only [mul_inv_rev,inv_inv,mul_assoc]
  simp_rw [he]
  change coefficient β^3*SU2WilsonConvolution.step β halfTrace ((rightPath s)⁻¹*s.1)=_
  rw [halfTrace_eigen]
  have hv : halfTrace ((rightPath s)⁻¹*s.1)=second s := by
    unfold second
    rw [← halfTrace_inv (s.1⁻¹*rightPath s)]
    simp only [mul_inv_rev,inv_inv]
  rw [hv]
  unfold second rightPath
  ring

def gaugeAction (g : Fin 6 → SU2) (s : State) : State :=
  (g 3*s.1*(g 0)⁻¹,
    g 0*s.2.1*(g 1)⁻¹,g 1*s.2.2.1*(g 2)⁻¹,g 2*s.2.2.2.1*(g 3)⁻¹,
    g 3*s.2.2.2.2.1*(g 4)⁻¹,g 4*s.2.2.2.2.2.1*(g 5)⁻¹,g 5*s.2.2.2.2.2.2*(g 0)⁻¹)

theorem first_gauge (g : Fin 6 → SU2) (s : State) : first (gaugeAction g s)=first s := by
  exact loop4_gauge (g 0) (g 1) (g 2) (g 3) s.2.1 s.2.2.1 s.2.2.2.1 s.1

theorem second_gauge (g : Fin 6 → SU2) (s : State) : second (gaugeAction g s)=second s := by
  have he : (g 3*s.1*(g 0)⁻¹)⁻¹*
      ((g 3*s.2.2.2.2.1*(g 4)⁻¹)*(g 4*s.2.2.2.2.2.1*(g 5)⁻¹)*(g 5*s.2.2.2.2.2.2*(g 0)⁻¹))=
      g 0*(s.1⁻¹*rightPath s)*(g 0)⁻¹ := by unfold rightPath; group
  change halfTrace ((g 3*s.1*(g 0)⁻¹)⁻¹*
      ((g 3*s.2.2.2.2.1*(g 4)⁻¹)*(g 4*s.2.2.2.2.2.1*(g 5)⁻¹)*(g 5*s.2.2.2.2.2.2*(g 0)⁻¹)))=second s
  rw [he,halfTrace_conjugate]
  rfl

theorem residual_gauge (g : Fin 6 → SU2) (s : State) : residual (gaugeAction g s)=residual s :=
  twoPlaquette_residual_gauge g s.2.1 s.2.2.1 s.2.2.2.1
    s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2 s.1

theorem meanChannel_gauge (g : Fin 6 → SU2) (s : State) : meanChannel (gaugeAction g s)=meanChannel s := by
  have he (r : State) : meanChannel r=first r*second r-residual r := by
    unfold residual sharedResidual sharedProduct first second meanChannel
    ring
  rw [he,first_gauge,second_gauge,residual_gauge,← he]

theorem trialVacuum_gauge (g : Fin 6 → SU2) (β t : ℝ) (s : State) :
    trialVacuum β t (gaugeAction g s)=trialVacuum β t s := by
  unfold trialVacuum
  rw [first_gauge]

private instance law_rightInvariant : law.IsMulRightInvariant := ⟨fun g => by
  letI : IsProbabilityMeasure (law.map (fun C => C*g)) := by infer_instance
  exact (law_eq_probability_haar (law.map (fun C => C*g))).symm⟩

private theorem product_measurableMul (G H : Type*) [MeasurableSpace G] [MeasurableSpace H]
    [Mul G] [Mul H] [MeasurableMul G] [MeasurableMul H] : MeasurableMul (G × H) where
  measurable_const_mul g :=
    ((measurable_const_mul g.1).comp measurable_fst).prodMk
      ((measurable_const_mul g.2).comp measurable_snd)
  measurable_mul_const g :=
    ((measurable_mul_const g.1).comp measurable_fst).prodMk
      ((measurable_mul_const g.2).comp measurable_snd)

instance haar_rightInvariant : haar.IsMulRightInvariant := by
  letI m2 : MeasurableMul (SU2 × SU2) := product_measurableMul _ _
  letI m3 : MeasurableMul (SU2 × SU2 × SU2) := product_measurableMul _ _
  letI m4 : MeasurableMul (SU2 × SU2 × SU2 × SU2) := product_measurableMul _ _
  letI m5 : MeasurableMul (SU2 × SU2 × SU2 × SU2 × SU2) := product_measurableMul _ _
  letI m6 : MeasurableMul (SU2 × SU2 × SU2 × SU2 × SU2 × SU2) := product_measurableMul _ _
  letI h2 : (law.prod law).IsMulRightInvariant := by infer_instance
  letI h3 : (law.prod (law.prod law)).IsMulRightInvariant := by infer_instance
  letI h4 : (law.prod (law.prod (law.prod law))).IsMulRightInvariant := by infer_instance
  letI h5 : (law.prod (law.prod (law.prod (law.prod law)))).IsMulRightInvariant := by infer_instance
  letI h6 : (law.prod (law.prod (law.prod (law.prod (law.prod law))))).IsMulRightInvariant := by infer_instance
  letI p6 : IsProbabilityMeasure (law.prod (law.prod (law.prod (law.prod (law.prod law))))) := by infer_instance
  unfold haar edgeLaw
  exact Measure.prod.instIsMulRightInvariant

/-- Actual Haar stationarity for bounded measurable observables of the full product transfer. -/
theorem step_haar_stationary (β : ℝ) (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s, |f s| ≤ B) : (∫ s, step β f s ∂haar)=∫ s, f s ∂haar := by
  letI := noise_probability β
  have hi : Integrable (fun p : State × State => f (p.1*p.2)) (haar.prod (noise β)) := by
    apply Integrable.of_bound (hf.comp continuous_mul.measurable).aestronglyMeasurable B
    filter_upwards with p
    simpa only [Real.norm_eq_abs,Function.comp_apply] using hb (p.1*p.2)
  unfold step
  rw [integral_integral_swap hi]
  simp_rw [integral_mul_right_eq_self]
  simp

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer
open QuaternionSU2Representation SU2WilsonConvolution SU2SharedPlaquetteProjection

private theorem trace_right_mean (U : SU2) : (∫ L, halfTrace (L*U) ∂law)=0 := by
  have he (L : SU2) : halfTrace (L*U)=halfTrace (U*L) := halfTrace_mul_comm L U
  simp_rw [he]
  rw [integral_mul_left_eq_self]
  exact (SU2TiltEnergyResponse.moment_values law).1

theorem haar_first_mean : (∫ s, first s ∂haar)=0 := by
  change (∫ s, halfTrace (leftPath s*s.1) ∂haar)=0
  rw [haar_path_integral (fun L R U => halfTrace (L*U)) first_measurable 1
    (fun L R U => halfTrace_bound (L*U))]
  simp only [integral_const,probReal_univ,one_smul]
  simp_rw [trace_right_mean]
  simp

theorem haar_first_lag (β : ℝ) : (∫ s, first s*step β first s ∂haar)=coefficient β^4/4 := by
  simp_rw [step_first]
  have he (s : State) : first s*(coefficient β^4*first s)=coefficient β^4*(first s^2) := by ring
  simp_rw [he]
  rw [integral_const_mul,haar_first_second_moment]
  ring

/-- A genuine stationary kinetic lag obstruction. Spatial vacuum normalization
and all four-dimensional quantum-field limits remain separate obligations. -/
theorem no_uniform_centered_kinetic_bound (q : ℝ) (hq : q < 1) :
    ∃ β : ℝ, 0 ≤ β ∧ q*(∫ s, first s^2 ∂haar) < ∫ s, first s*step β first s ∂haar := by
  obtain ⟨β,hβ,hc⟩ := no_uniform_fixed_word_factor 4 q hq
  refine ⟨β,hβ,?_⟩
  rw [haar_first_lag,haar_first_second_moment]
  linarith

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer
open ProbabilityTheory

/-- Genuine Markov kernel: sample seven independent Wilson increments and update
all seven links by right multiplication. -/
def transition (β : ℝ) : Kernel State State :=
  (Kernel.prod Kernel.id (Kernel.const State (noise β))).map (fun p : State × State => p.1*p.2)

theorem transition_markov (β : ℝ) : IsMarkovKernel (transition β) := by
  letI := noise_probability β
  exact Kernel.IsMarkovKernel.map _ continuous_mul.measurable

theorem transition_eq_map (β : ℝ) (s : State) :
    transition β s=(noise β).map (fun v => s*v) := by
  letI := noise_probability β
  rw [transition,Kernel.map_apply _ continuous_mul.measurable,Kernel.prod_apply,
    Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod]
  have hm : Measurable (Prod.mk s : State → State × State) := by fun_prop
  rw [Measure.map_map continuous_mul.measurable hm]
  rfl

theorem transition_integral (β : ℝ) (f : State → ℝ) (hf : Measurable f) (s : State) :
    (∫ r, f r ∂transition β s)=step β f s := by
  rw [transition_eq_map,integral_map ((continuous_const_mul s).measurable).aemeasurable hf.aestronglyMeasurable]
  rfl

/-- Stationarity against every bounded measurable probe for the actual kernel. -/
theorem transition_integral_stationary (β : ℝ) (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s, |f s| ≤ B) :
    (∫ s, ∫ r, f r ∂transition β s ∂haar)=∫ s, f s ∂haar := by
  simp_rw [transition_integral β f hf]
  exact step_haar_stationary β f hf B hb

theorem transition_first_lag (β : ℝ) :
    (∫ s, first s*(∫ r, first r ∂transition β s) ∂haar)=SU2WilsonConvolution.coefficient β^4/4 := by
  simp_rw [transition_integral β first first_measurable]
  exact haar_first_lag β

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer
open QuaternionSU2Representation SU2SharedPlaquetteProjection

theorem haar_product_second_moment : (∫ s, (first s*second s)^2 ∂haar)=(1/16:ℝ) := by
  have hm := (first_measurable.mul second_measurable).pow_const 2
  have hb (L R U : SU2) : |sharedProduct L R U^2| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) (sharedProduct_bound L R U) 2
  change (∫ s, sharedProduct (leftPath s) (rightPath s) s.1^2 ∂haar)=_
  rw [haar_path_integral (fun L R U => sharedProduct L R U^2) hm 1 hb]
  simp_rw [fun U => (shared_projection_second_moments U).1]
  simp

theorem haar_channels_orthogonal : (∫ s, meanChannel s*residual s ∂haar)=0 := by
  have hm : Integrable (fun s => meanChannel s^2) haar := by
    apply Integrable.of_bound (meanChannel_measurable.pow_const 2).aestronglyMeasurable 1
    filter_upwards with s
    rw [Real.norm_eq_abs,abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) (meanChannel_bound s) 2
  have hq : Integrable (fun s => residual s^2) haar := by
    apply Integrable.of_bound (residual_measurable.pow_const 2).aestronglyMeasurable 4
    filter_upwards with s
    rw [Real.norm_eq_abs,abs_pow]
    simpa only [show (2:ℝ)^2=4 by norm_num] using
      pow_le_pow_left₀ (abs_nonneg _) (residual_bound s) 2
  have hmq : Integrable (fun s => meanChannel s*residual s) haar := by
    apply Integrable.of_bound (meanChannel_measurable.mul residual_measurable).aestronglyMeasurable 2
    filter_upwards with s
    change ‖meanChannel s*residual s‖ ≤ 2
    rw [Real.norm_eq_abs,abs_mul]
    simpa using mul_le_mul (meanChannel_bound s) (residual_bound s) (abs_nonneg _) (by norm_num)
  have he (s : State) : (first s*second s)^2=
      (meanChannel s^2+2*(meanChannel s*residual s))+residual s^2 := by
    have hp : first s*second s=meanChannel s+residual s := by
      unfold meanChannel residual sharedResidual sharedProduct first second
      ring
    rw [hp]
    ring
  have hadd := integral_add (hm.add (hmq.const_mul 2)) hq
  have hinner := integral_add hm (hmq.const_mul 2)
  simp only [Pi.add_apply] at hadd hinner
  have h := haar_product_second_moment
  simp_rw [he] at h
  rw [hadd,hinner,integral_const_mul,haar_mean_second_moment,haar_residual_second_moment] at h
  linarith

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkTransfer
