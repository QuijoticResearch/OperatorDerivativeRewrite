import Foundation.PoissonExponentialEntropy

/-! Curvature of the actual Poisson jump-generator expression, linked to
the complete maximal source graphs. Forward source Bochner energy differs
from the generator's pointwise carre du champ. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonJumpCurvature
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonCoherentVectors PoissonExponentialEntropy

def jumpGradient (f : ℕ → ℝ) (n : ℕ) : ℝ := f (n+1)-f n

def jumpGenerator (rate : ℝ≥0) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (rate : ℝ)*jumpGradient f n+(n : ℝ)*(f (n-1)-f n)

def carre (rate : ℝ≥0) (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1/2 : ℝ)*(jumpGenerator rate (fun k => f k*g k) n-
    f n*jumpGenerator rate g n-g n*jumpGenerator rate f n)

def gamma (rate : ℝ≥0) (f : ℕ → ℝ) : ℕ → ℝ := carre rate f f

def gamma2 (rate : ℝ≥0) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1/2 : ℝ)*jumpGenerator rate (gamma rate f) n-carre rate f (jumpGenerator rate f) n

theorem carre_eq_differences (rate : ℝ≥0) (f g : ℕ → ℝ) (n : ℕ) :
    carre rate f g n=(rate : ℝ)/2*jumpGradient f n*jumpGradient g n+
      (n : ℝ)/2*(f n-f (n-1))*(g n-g (n-1)) := by
  unfold carre jumpGenerator jumpGradient
  ring

theorem gamma_eq_differences (rate : ℝ≥0) (f : ℕ → ℝ) (n : ℕ) :
    gamma rate f n=(rate : ℝ)/2*(jumpGradient f n)^2+(n : ℝ)/2*(f n-f (n-1))^2 := by
  rw [gamma,carre_eq_differences]
  ring

theorem gamma_nonneg (rate : ℝ≥0) (f : ℕ → ℝ) (n : ℕ) : 0≤gamma rate f n := by
  rw [gamma_eq_differences]
  positivity

theorem gamma2_decomposition (rate : ℝ≥0) (f : ℕ → ℝ) (n : ℕ) :
    gamma2 rate f n=
      (rate : ℝ)^2/4*(f (n+2)-2*f (n+1)+f n)^2+
      (n : ℝ)*((n-1 : ℕ) : ℝ)/4*(f n-2*f (n-1)+f (n-2))^2+
      (rate : ℝ)*(n : ℝ)/2*(f (n+1)-2*f n+f (n-1))^2+
      (3/4 : ℝ)*(rate : ℝ)*(jumpGradient f n)^2+(n : ℝ)/4*(f n-f (n-1))^2 := by
  cases n with
  | zero => simp [gamma2,jumpGenerator,gamma_eq_differences,carre_eq_differences,jumpGradient]; ring
  | succ n =>
    cases n with
    | zero => simp [gamma2,jumpGenerator,gamma_eq_differences,carre_eq_differences,jumpGradient]; ring
    | succ n =>
      simp [gamma2,jumpGenerator,gamma_eq_differences,carre_eq_differences,jumpGradient,
        Nat.succ_eq_add_one,Nat.add_assoc,Nat.cast_add,Nat.cast_ofNat]
      ring

theorem gamma2_half_lower (rate : ℝ≥0) (f : ℕ → ℝ) (n : ℕ) :
    (1/2 : ℝ)*gamma rate f n ≤ gamma2 rate f n := by
  rw [gamma2_decomposition,gamma_eq_differences]
  have h1 : 0≤(rate : ℝ)^2/4*(f (n+2)-2*f (n+1)+f n)^2 := by positivity
  have h2 : 0≤(n : ℝ)*((n-1 : ℕ) : ℝ)/4*(f n-2*f (n-1)+f (n-2))^2 := by positivity
  have h3 : 0≤(rate : ℝ)*(n : ℝ)/2*(f (n+1)-2*f n+f (n-1))^2 := by positivity
  nlinarith [mul_nonneg rate.coe_nonneg (sq_nonneg (jumpGradient f n))]

theorem gamma_count (rate : ℝ≥0) (n : ℕ) :
    gamma rate (fun k => (k : ℝ)) n=(rate : ℝ)/2+(n : ℝ)/2 := by
  cases n <;> simp [gamma_eq_differences,jumpGradient,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] <;> ring

theorem gamma2_count (rate : ℝ≥0) (n : ℕ) :
    gamma2 rate (fun k => (k : ℝ)) n=3*(rate : ℝ)/4+(n : ℝ)/4 := by
  cases n with
  | zero => simp [gamma2_decomposition,jumpGradient]; ring
  | succ n =>
    cases n with
    | zero => simp [gamma2_decomposition,jumpGradient]; ring
    | succ n => simp [gamma2_decomposition,jumpGradient,Nat.succ_eq_add_one,Nat.add_assoc,Nat.cast_add]; ring

theorem no_larger_pointwise_curvature (rate : ℝ≥0) (κ : ℝ) (hκ : 1/2<κ) :
    ∃ n : ℕ, gamma2 rate (fun k => (k : ℝ)) n<κ*gamma rate (fun k => (k : ℝ)) n := by
  have hp : 0<2*κ-1 := by linarith
  obtain ⟨n,hn⟩ := exists_nat_gt ((rate : ℝ)*(3-2*κ)/(2*κ-1))
  have hh := (div_lt_iff₀ hp).mp hn
  refine ⟨n, ?_⟩
  rw [gamma2_count,gamma_count]
  nlinarith [hh]

theorem number_graph_generator (rate : ℝ≥0) (hr : 0<rate)
    (f : ScalarL2 rate) (g : FieldL2 rate) (h : ScalarL2 rate)
    (hD : (f,g)∈(maximalDifference rate hr).graph) (hδ : (g,h)∈(maximalDivergence rate hr).graph) :
    ∀ n : ℕ, h n=-jumpGenerator rate f n := by
  rw [maximalDifference_graph] at hD
  rw [maximalDivergence_graph] at hδ
  intro n
  cases n with
  | zero =>
    have he := hδ 0
    rw [maximalDivergenceExpr,hD 0] at he
    simp only [jumpGenerator,jumpGradient,Nat.cast_zero,zero_mul,add_zero]
    simpa only [neg_mul] using he
  | succ n =>
    have he := hδ (n+1)
    rw [maximalDivergenceExpr,hD n,hD (n+1)] at he
    simp only [jumpGenerator,jumpGradient,Nat.add_sub_cancel_right,Nat.cast_add,Nat.cast_one]
    linear_combination he

theorem gradient_generator_commutation (rate : ℝ≥0) (f : ℕ → ℝ) (n : ℕ) :
    jumpGradient (jumpGenerator rate f) n=jumpGenerator rate (jumpGradient f) n-jumpGradient f n := by
  cases n <;> simp [jumpGenerator,jumpGradient,Nat.succ_eq_add_one,Nat.add_assoc,Nat.cast_add,Nat.cast_one] <;> ring

def forwardEnergy (rate : ℝ≥0) (f : ℕ → ℝ) (n : ℕ) : ℝ := (rate : ℝ)*(jumpGradient f n)^2

def forwardBochner (rate : ℝ≥0) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1/2 : ℝ)*jumpGenerator rate (forwardEnergy rate f) n-
    (rate : ℝ)*jumpGradient f n*jumpGradient (jumpGenerator rate f) n

theorem forwardBochner_identity (rate : ℝ≥0) (f : ℕ → ℝ) (n : ℕ) :
    forwardBochner rate f n=forwardEnergy rate f n+(rate : ℝ)*gamma rate (jumpGradient f) n := by
  rw [forwardBochner,gradient_generator_commutation]
  unfold forwardEnergy gamma carre jumpGenerator jumpGradient
  ring

theorem forwardBochner_one_lower (rate : ℝ≥0) (f : ℕ → ℝ) (n : ℕ) :
    forwardEnergy rate f n ≤ forwardBochner rate f n := by
  rw [forwardBochner_identity]
  nlinarith [mul_nonneg rate.coe_nonneg (gamma_nonneg rate (jumpGradient f) n)]

theorem forward_energy_not_generator_carre (rate : ℝ≥0) (hr : 0<rate) :
    forwardEnergy rate (fun k => (k : ℝ)) 0≠gamma rate (fun k => (k : ℝ)) 0 := by
  rw [gamma_count]
  simp only [forwardEnergy,jumpGradient,Nat.cast_one,Nat.cast_zero,sub_zero,one_pow,mul_one,zero_div,add_zero]
  have hp : (0 : ℝ)<rate := hr
  linarith

private theorem exponential_succ (θ : ℝ) (n : ℕ) :
    exponential θ (n+1)=Real.exp θ*exponential θ n := by
  simp only [exponential,Nat.cast_add,Nat.cast_one,mul_add,Real.exp_add]
  ring

private theorem exponential_neg_succ (θ : ℝ) (n : ℕ) :
    Real.exp (-θ)*exponential θ (n+1)=exponential θ n := by
  rw [exponential,exponential,← Real.exp_add]
  push_cast
  congr 1
  ring

theorem gamma_exponential (rate : ℝ≥0) (θ : ℝ) (n : ℕ) :
    gamma rate (exponential θ) n=
      ((rate : ℝ)/2*(Real.exp θ-1)^2+(n : ℝ)/2*(1-Real.exp (-θ))^2)*exponential (2*θ) n := by
  cases n with
  | zero => simp [gamma_eq_differences,jumpGradient,exponential]
  | succ n =>
    rw [gamma_eq_differences,jumpGradient,Nat.add_sub_cancel_right,
      exponential_succ θ (n+1),← exponential_neg_succ θ n,← exponential_square θ (n+1)]
    ring

theorem gamma_exponential_integrable (rate : ℝ≥0) (θ : ℝ) :
    Integrable (gamma rate (exponential θ)) (poissonLaw rate) := by
  have ha := ((exponential_memLp rate (2*θ)).integrable (by norm_num)).const_mul
    ((rate : ℝ)/2*(Real.exp θ-1)^2)
  have hb := ((count_exponential_memLp rate (2*θ)).integrable (by norm_num)).const_mul
    ((1/2 : ℝ)*(1-Real.exp (-θ))^2)
  exact (ha.add hb).congr (Eventually.of_forall fun n => by
    rw [gamma_exponential]
    simp only [Pi.add_apply]
    ring)

theorem gamma_exponential_integral (rate : ℝ≥0) (θ : ℝ) :
    (∫ n, gamma rate (exponential θ) n ∂poissonLaw rate)=
      (rate : ℝ)*Real.exp ((rate : ℝ)*(Real.exp (2*θ)-1))*(Real.exp θ-1)^2 := by
  let A := (rate : ℝ)/2*(Real.exp θ-1)^2
  let B := (1/2 : ℝ)*(1-Real.exp (-θ))^2
  have he : gamma rate (exponential θ)=(fun n => A*exponential (2*θ) n+B*((n : ℝ)*exponential (2*θ) n)) := by
    funext n
    rw [gamma_exponential]
    dsimp [A,B]
    ring
  have ha := ((exponential_memLp rate (2*θ)).integrable (by norm_num)).const_mul A
  have hb := ((count_exponential_memLp rate (2*θ)).integrable (by norm_num)).const_mul B
  rw [he,integral_add ha hb,integral_const_mul,integral_const_mul,
    exponential_integral,count_exponential_integral]
  have hp : Real.exp (-θ)*Real.exp θ=1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  have hs : (Real.exp θ)^2=Real.exp (2*θ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (1-Real.exp (-θ))^2*Real.exp (2*θ)=(Real.exp θ-1)^2 := by
    rw [← hs,← mul_pow]
    have hh : (1-Real.exp (-θ))*Real.exp θ=Real.exp θ-1 := by nlinarith [hp]
    rw [hh]
  dsimp [A,B]
  linear_combination ((rate : ℝ)*Real.exp ((rate : ℝ)*(Real.exp (2*θ)-1))/2)*hc

theorem gamma_exponential_eq_source_energy (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) :
    (∫ n, gamma rate (exponential θ) n ∂poissonLaw rate)=‖(Real.exp θ-1) • field rate θ‖^2 := by
  rw [gamma_exponential_integral,exponential_difference_energy rate hr θ]

theorem exponential_number_domain (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) :
    ∃ g : FieldL2 rate, ∃ h : ScalarL2 rate,
      (scalar rate θ,g)∈(maximalDifference rate hr).graph ∧ (g,h)∈(maximalDivergence rate hr).graph := by
  refine ⟨(Real.exp θ-1) • field rate θ,(Real.exp θ-1) • divergenceScalar rate θ,
    exponential_difference_graph rate hr θ, ?_⟩
  simpa only [Prod.smul_mk] using
    (maximalDivergence rate hr).graph.smul_mem (Real.exp θ-1) (exponential_divergence_graph rate hr θ)

theorem gamma_quadratic_entropy_obstruction (rate : ℝ≥0) (hr : 0<rate) (C : ℝ) (hC : 0≤C) :
    C*(∫ n, gamma rate (exponential (C+1)) n ∂poissonLaw rate)<
      entropySq (poissonLaw rate) (exponential (C+1)) := by
  let θ := C+1
  have hθ : 0<θ := by dsimp [θ]; linarith
  change C*(∫ n, gamma rate (exponential θ) n ∂poissonLaw rate)<entropySq (poissonLaw rate) (exponential θ)
  rw [gamma_exponential_integral,exponential_entropy]
  have he : 1≤Real.exp θ := Real.one_le_exp_iff.mpr hθ.le
  have hs : Real.exp (2*θ)=(Real.exp θ)^2 := by rw [show 2*θ=θ+θ by ring,Real.exp_add,pow_two]
  have hd : (Real.exp θ-1)^2 ≤ Real.exp (2*θ) := by rw [hs]; nlinarith
  have hb : C*(Real.exp θ-1)^2 < 2*θ*Real.exp (2*θ)-Real.exp (2*θ)+1 := by
    have hm := mul_le_mul_of_nonneg_left hd hC
    have hp := Real.exp_pos (2*θ)
    dsimp [θ] at *
    nlinarith
  have hp : 0<(rate : ℝ)*Real.exp ((rate : ℝ)*(Real.exp (2*θ)-1)) := mul_pos hr (Real.exp_pos _)
  have hm := mul_lt_mul_of_pos_left hb hp
  nlinarith [hm]

theorem actual_curvature_entropy_counterexample (rate : ℝ≥0) (hr : 0<rate) (C : ℝ) (hC : 0≤C) :
    ∃ f : ScalarL2 rate, ∃ g : FieldL2 rate, ∃ h : ScalarL2 rate,
      (f,g)∈(maximalDifference rate hr).graph ∧ (g,h)∈(maximalDivergence rate hr).graph ∧
        Integrable (gamma rate f) (poissonLaw rate) ∧
        Integrable (fun n => (f n)^2*Real.log ((f n)^2)) (poissonLaw rate) ∧
          C*(∫ n, gamma rate f n ∂poissonLaw rate)<entropySq (poissonLaw rate) (fun n => f n) := by
  let θ := C+1
  obtain ⟨g,h,hD,hδ⟩ := exponential_number_domain rate hr θ
  have hf : (scalar rate θ : ℕ → ℝ)=exponential θ := funext (scalar_apply rate hr θ)
  refine ⟨scalar rate θ,g,h,hD,hδ, ?_, ?_, ?_⟩
  · rw [hf]
    exact gamma_exponential_integrable rate θ
  · simpa only [scalar_apply rate hr θ] using exponential_entropy_integrable rate θ
  · rw [hf]
    exact gamma_quadratic_entropy_obstruction rate hr C hC

theorem diffusion_chain_rule_failure (rate : ℝ≥0) (hr : 0<rate) :
    gamma rate (exponential 1) 0>(Real.exp 0)^2*gamma rate (fun k => (k : ℝ)) 0 := by
  rw [gamma_exponential,gamma_count]
  simp only [Nat.cast_zero,zero_div,zero_mul,add_zero,exponential,mul_zero,Real.exp_zero,one_pow,mul_one,one_mul]
  have he : (2 : ℝ)<Real.exp 1 := by
    have hh := Real.add_one_lt_exp (by norm_num : (1 : ℝ)≠0)
    norm_num at hh
    exact hh
  have hs : (1 : ℝ)<(Real.exp 1-1)^2 := by nlinarith
  simpa only [mul_one] using mul_lt_mul_of_pos_left hs
    (by exact div_pos hr (by norm_num : (0 : ℝ)<2))

theorem diffusion_chain_rule_ae_failure (rate : ℝ≥0) (hr : 0<rate) :
    ¬ (∀ᵐ n ∂poissonLaw rate, gamma rate (exponential 1) n=
      (Real.exp (n : ℝ))^2*gamma rate (fun k => (k : ℝ)) n) := by
  intro hAE
  have he := ae_eq_implies_pointwise rate hr hAE 0
  exact (ne_of_gt (diffusion_chain_rule_failure rate hr)) (by simpa only [Nat.cast_zero] using he)

theorem forwardEnergy_exponential (rate : ℝ≥0) (θ : ℝ) (n : ℕ) :
    forwardEnergy rate (exponential θ) n=(rate : ℝ)*(Real.exp θ-1)^2*exponential (2*θ) n := by
  rw [forwardEnergy,jumpGradient,exponential_succ,← exponential_square θ n]
  ring

theorem forwardEnergy_exponential_integrable (rate : ℝ≥0) (θ : ℝ) :
    Integrable (forwardEnergy rate (exponential θ)) (poissonLaw rate) := by
  exact (((exponential_memLp rate (2*θ)).integrable (by norm_num)).const_mul
    ((rate : ℝ)*(Real.exp θ-1)^2)).congr (Eventually.of_forall fun n => (forwardEnergy_exponential rate θ n).symm)

theorem forwardEnergy_exponential_integral (rate : ℝ≥0) (θ : ℝ) :
    (∫ n, forwardEnergy rate (exponential θ) n ∂poissonLaw rate)=
      (rate : ℝ)*Real.exp ((rate : ℝ)*(Real.exp (2*θ)-1))*(Real.exp θ-1)^2 := by
  simp only [forwardEnergy_exponential]
  rw [integral_const_mul,exponential_integral]
  ring

theorem forward_bochner_entropy_obstruction (rate : ℝ≥0) (hr : 0<rate) (C : ℝ) (hC : 0≤C) :
    C*(∫ n, forwardEnergy rate (exponential (C+1)) n ∂poissonLaw rate)<
      entropySq (poissonLaw rate) (exponential (C+1)) := by
  have he : (∫ n, forwardEnergy rate (exponential (C+1)) n ∂poissonLaw rate)=
      ∫ n, gamma rate (exponential (C+1)) n ∂poissonLaw rate := by
    rw [forwardEnergy_exponential_integral,gamma_exponential_integral]
  rw [he]
  exact gamma_quadratic_entropy_obstruction rate hr C hC

end OperatorDerivativeRewrite.Foundation.PoissonJumpCurvature

