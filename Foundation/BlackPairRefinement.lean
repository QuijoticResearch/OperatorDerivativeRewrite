import Foundation.ComplexFourthRootNoise

/-! Endpoint memory obstructs universal adjacent-pair refinement, already on a
full-support finite reset-chain law. Terminal-only semigroup residuals have a
separate positive refinement identity. No sticky-flow realization is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BlackPairRefinement

abbrev Sample := Bool × Bool × Bool

def probability : Measure Sample := (PMF.uniformOfFintype Sample).toMeasure
instance probability_isProbability : IsProbabilityMeasure probability := by
  unfold probability
  infer_instance

def sign (b : Bool) : ℝ := if b then 1 else -1

def coarse (w : Sample) : ℝ := sign w.1 * sign w.2.2

def adjacent (g h : Bool → Bool → ℝ) (w : Sample) : ℝ :=
  g w.1 w.2.1 + h w.2.1 w.2.2

theorem sample_singleton (w : Sample) : probability {w} = (1/8 : ℝ≥0∞) := by
  simp [probability, PMF.uniformOfFintype_apply, Fintype.card_prod]

theorem integral_formula (f : Sample → ℝ) :
    (∫ w, f w ∂probability) =
      (f (true,true,true) + f (true,true,false) + f (true,false,true) +
        f (true,false,false) + f (false,true,true) + f (false,true,false) +
        f (false,false,true) + f (false,false,false))/8 := by
  rw [probability, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_bool,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [smul_eq_mul]
  ring

/-- Actual three-time law factors as initial half times two reset transitions. -/
theorem reset_chain_factorization (a b c : Bool) :
    probability.real {(a,b,c)} = (1/2 : ℝ) * (1/2) * (1/2) := by
  norm_num [Measure.real, sample_singleton]

/-- Coarse observable is centered for EVERY initial state of this reset chain. -/
theorem coarse_slice_centered (a : Bool) :
    ∑ c : Bool, (1/2 : ℝ) * (sign a * sign c) = 0 := by
  simp [sign]

theorem coarse_energy : (∫ w, (coarse w)^2 ∂probability) = 1 := by
  rw [integral_formula]
  norm_num [coarse, sign]

/-- Quantitative obstruction: completing the adjacent-pair span cannot help. -/
theorem coarse_orthogonal_adjacent (g h : Bool → Bool → ℝ) :
    (∫ w, coarse w * adjacent g h w ∂probability) = 0 := by
  rw [integral_formula]
  simp only [coarse, adjacent, sign, Bool.false_eq_true, ite_false, ite_true]
  ring

theorem approximation_error_identity (g h : Bool → Bool → ℝ) :
    (∫ w, (coarse w - adjacent g h w)^2 ∂probability) =
      1 + ∫ w, (adjacent g h w)^2 ∂probability := by
  rw [integral_formula, integral_formula]
  simp only [coarse, adjacent, sign, Bool.false_eq_true, ite_false, ite_true]
  ring

theorem approximation_error_lower_bound (g h : Bool → Bool → ℝ) :
    1 ≤ ∫ w, (coarse w - adjacent g h w)^2 ∂probability := by
  rw [approximation_error_identity]
  have hp : 0 ≤ ∫ w, (adjacent g h w)^2 ∂probability :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

theorem no_adjacent_refinement_ae (g h : Bool → Bool → ℝ) :
    ¬ coarse =ᵐ[probability] adjacent g h := by
  intro he
  have hz : (∫ w, (coarse w - adjacent g h w)^2 ∂probability) = 0 := by
    calc
      _ = ∫ _ : Sample, (0 : ℝ) ∂probability := integral_congr_ae
        (he.mono (fun w hw => by rw [hw]; simp))
      _ = 0 := by simp
  have hb := approximation_error_lower_bound g h
  linarith

/-- No sequence of unaugmented adjacent-pair functions can approximate the
coarse slice in mean square under the actual full-support probability law. -/
theorem no_mean_square_approximation (g h : ℕ → Bool → Bool → ℝ) :
    ¬ Tendsto (fun n => ∫ w, (coarse w - adjacent (g n) (h n) w)^2 ∂probability)
      atTop (nhds 0) := by
  intro ht
  have hb : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Eventually.of_forall (fun n => approximation_error_lower_bound (g n) (h n)))
  norm_num at hb

/-- Keeping the original starting state restores a centered refinement:
the first increment is zero, the second is the coarse product itself. -/
theorem augmented_refinement_centered (a _b : Bool) :
    ∑ c : Bool, (1/2 : ℝ) * (0 + sign a * sign c) = 0 := by
  simpa only [zero_add] using coarse_slice_centered a

section FiniteKernels
variable {S : Type*} [Fintype S]

def action (P : S → S → ℝ) (f : S → ℝ) (a : S) : ℝ := ∑ b, P a b * f b

theorem residual_centered (P : S → S → ℝ) (f : S → ℝ)
    (hP : ∀ a, ∑ b, P a b = 1) (a : S) :
    ∑ b, P a b * (f b - action P f a) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hP, one_mul]
  exact sub_self _

/-- Matrix composition agrees with two successive finite kernel actions. -/
theorem action_comp (P Q : S → S → ℝ) (f : S → ℝ) (a : S) :
    action (fun x z => ∑ y, P x y * Q y z) f a = action P (action Q f) a := by
  simp only [action, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Terminal-only residuals refine in the unaugmented state, unlike arbitrary
start-dependent slice functions. For stochastic P,Q, the iterated action is
the two-step conditional mean; the algebra also permits signed matrices. -/
theorem terminal_residual_refinement (P Q : S → S → ℝ) (f : S → ℝ) (a b c : S) :
    f c - action P (action Q f) a =
      (action Q f b - action P (action Q f) a) + (f c - action Q f b) := by ring

/-- Both refined increments have the correct conditional centering. -/
theorem terminal_refinement_centering (P Q : S → S → ℝ) (f : S → ℝ)
    (hP : ∀ a, ∑ b, P a b = 1) (hQ : ∀ b, ∑ c, Q b c = 1) (a b : S) :
    (∑ x, P a x * (action Q f x - action P (action Q f) a)) = 0 ∧
      (∑ y, Q b y * (f y - action Q f b)) = 0 :=
  ⟨residual_centered P (action Q f) hP a, residual_centered Q f hQ b⟩

/-- Conditional variance decomposition, retaining the actual finite kernel weights. -/
theorem conditional_variance_split (Q : S → S → ℝ) (f : S → ℝ)
    (hQ : ∀ b, ∑ c, Q b c = 1) (b : S) (m : ℝ) :
    (∑ c, Q b c * (f c - m)^2) = (action Q f b - m)^2 +
      ∑ c, Q b c * (f c - action Q f b)^2 := by
  have he (c : S) : Q b c * (f c - m)^2 =
      Q b c * (action Q f b - m)^2 + Q b c * (f c - action Q f b)^2 +
        (2*(action Q f b-m)) * (Q b c * (f c - action Q f b)) := by ring
  simp_rw [he, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hQ, one_mul, ← Finset.mul_sum,
    residual_centered Q f hQ b, mul_zero, add_zero]

/-- The terminal-residual refinement is isometric in divergence-output energy.
Nonnegative stochastic kernels make these sums genuine squared L2 norms. -/
theorem terminal_refinement_energy (P Q : S → S → ℝ) (f : S → ℝ)
    (hQ : ∀ b, ∑ c, Q b c = 1) (a : S) :
    (∑ b, P a b * (∑ c, Q b c * (f c - action P (action Q f) a)^2)) =
      (∑ b, P a b * (action Q f b - action P (action Q f) a)^2) +
        ∑ b, P a b * (∑ c, Q b c * (f c - action Q f b)^2) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_add, conditional_variance_split Q f hQ b (action P (action Q f) a)]

end FiniteKernels
end OperatorDerivativeRewrite.Foundation.BlackPairRefinement
