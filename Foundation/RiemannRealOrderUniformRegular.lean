import Foundation.RiemannRealOrderUniformEndpoint

/-! Uniform regular coefficients in the actual fourth density derivative.
Only the third phase factor remains singular near zero; it occurs linearly. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderUniformRegular
open RiemannThetaComplexKernel RiemannRealOrderFractionalJets
open RiemannRealOrderFractionalRemainder RiemannRealOrderUniformEndpoint

private theorem kernel_jet_bound : ∃ B : ℝ, 0 ≤ B ∧
    ∀ n : ℕ, n < 5 → ∀ u ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv n kernelComplex (u : ℂ)‖ ≤ B := by
  choose C hC using fun n : ℕ => isCompact_Icc.exists_bound_of_continuousOn
    (kernel_derivative_continuous n).continuousOn
  let B : ℝ := ∑ n ∈ Finset.range 5, |C n|
  refine ⟨B,Finset.sum_nonneg (fun _ _ => abs_nonneg _),?_⟩
  intro n hn u hu
  exact (hC n u hu).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr hn)))

theorem exponential_norm_bound (a t u : ℝ) (ha : 1 ≤ a) (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖exponential a t (u : ℂ)‖ ≤ Real.exp |t| := by
  have hp : u^(2*a) ≤ 1 := Real.rpow_le_one hu.1 hu.2 (by linarith)
  have hs : t*u^(2*a) ≤ |t| :=
    (le_abs_self _).trans (by
      rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg hu.1 _)]
      exact mul_le_of_le_one_right (abs_nonneg t) hp)
  simp only [exponential,← Complex.ofReal_cpow hu.1,← Complex.ofReal_mul,
    ← Complex.ofReal_exp,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr hs

theorem low_phase_norm_bound (a t u : ℝ) (ha : 1 ≤ a) (ha5 : a ≤ 5/4)
    (hu : u ∈ Icc (0 : ℝ) 1) (n : ℕ) (hn : n=1 ∨ n=2) :
    ‖phaseJet a t n (u : ℂ)‖ ≤ 6*|t| := by
  have he : 0 ≤ 2*a-(n : ℝ) := by rcases hn with rfl | rfl <;> norm_num <;> linarith
  have hp : u^(2*a-(n : ℝ)) ≤ 1 := Real.rpow_le_one hu.1 hu.2 he
  have hf : |falling (2*a) n| ≤ 6 := by
    rcases hn with rfl | rfl
    · norm_num [falling,Finset.prod_range_succ,abs_of_nonneg (by linarith : 0 ≤ 2*a)]
      linarith
    · have h0 : 0 ≤ 2*a := by linarith
      have h1 : 0 ≤ 2*a-1 := by linarith
      norm_num only [falling,Finset.prod_range_succ,Finset.prod_range_zero,
        Nat.cast_zero,Nat.cast_one,mul_one,one_mul,sub_zero]
      rw [abs_mul,abs_of_nonneg h0,abs_of_nonneg h1]
      have h := mul_le_mul (by linarith : 2*a ≤ 3) (by linarith : 2*a-1 ≤ 2) h1
        (by norm_num : (0 : ℝ) ≤ 3)
      norm_num at h
      exact h
  rw [phaseJet_real a t u n hu.1,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hu.1 _)]
  calc
    _ ≤ (|t| * 6)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hf (abs_nonneg t)) hp
        (Real.rpow_nonneg hu.1 _) (by positivity)
    _ = _ := by ring

private theorem fourth_polynomial_norm (e p q r k0 k1 k2 k3 k4 : ℂ) (B : ℝ)
    (he : ‖e‖ ≤ B) (hp : ‖p‖ ≤ B) (hq : ‖q‖ ≤ B)
    (h0 : ‖k0‖ ≤ B) (h1 : ‖k1‖ ≤ B) (h2 : ‖k2‖ ≤ B)
    (h3 : ‖k3‖ ≤ B) (h4 : ‖k4‖ ≤ B) :
    ‖e*(k4+4*p*k3+6*(q+p^2)*k2+4*(r+3*p*q+p^3)*k1+
      (4*p*r+3*q^2+6*p^2*q+p^4)*k0)‖ ≤
      B*(B+4*B*B+6*(B+B^2)*B+4*(‖r‖+3*B*B+B^3)*B+
        (4*B*‖r‖+3*B^2+6*B^2*B+B^4)*B) := by
  have hs (x y : ℂ) (v w : ℝ) (hx : ‖x‖ ≤ v) (hy : ‖y‖ ≤ w) :
      ‖x+y‖ ≤ v+w := (norm_add_le _ _).trans (add_le_add hx hy)
  repeat' first
    | assumption
    | exact le_rfl
    | (solve | norm_num)
    | (rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (by assumption) _)
    | apply hs
    | apply norm_mul_le_of_le

theorem regularFourth_uniform_pointwise (t : ℝ) : ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
    ∀ a : ℝ, 1 ≤ a → a ≤ 5/4 → ∀ u ∈ Icc (0 : ℝ) 1,
      ‖regularFourth a t (u : ℂ)‖ ≤ C*‖phaseJet a t 3 (u : ℂ)‖+D := by
  obtain ⟨K,hK,hKjet⟩ := kernel_jet_bound
  let B : ℝ := Real.exp |t|+6*|t|+K+1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let C : ℝ := 4*B^2+4*B^3
  let D : ℝ := B*(B+4*B*B+6*(B+B^2)*B+4*(3*B*B+B^3)*B+
    (3*B^2+6*B^2*B+B^4)*B)
  refine ⟨C,D,by dsimp [C]; positivity,by dsimp [D]; positivity,?_⟩
  intro a ha ha5 u hu
  have he : ‖exponential a t (u : ℂ)‖ ≤ B :=
    (exponential_norm_bound a t u ha hu).trans (by dsimp [B]; linarith [abs_nonneg t])
  have hp (n : ℕ) (hn : n=1 ∨ n=2) : ‖phaseJet a t n (u : ℂ)‖ ≤ B :=
    (low_phase_norm_bound a t u ha ha5 hu n hn).trans
      (by dsimp [B]; linarith [Real.exp_pos |t|])
  have hk (n : ℕ) (hn : n < 5) : ‖iteratedDeriv n kernelComplex (u : ℂ)‖ ≤ B :=
    (hKjet n hn u hu).trans (by dsimp [B]; linarith [Real.exp_pos |t|,abs_nonneg t])
  have hk0 : ‖kernelComplex (u : ℂ)‖ ≤ B := by simpa only [iteratedDeriv_zero] using hk 0 (by norm_num)
  have h := fourth_polynomial_norm (exponential a t (u : ℂ))
    (phaseJet a t 1 (u : ℂ)) (phaseJet a t 2 (u : ℂ)) (phaseJet a t 3 (u : ℂ))
    (kernelComplex (u : ℂ)) (iteratedDeriv 1 kernelComplex (u : ℂ))
    (iteratedDeriv 2 kernelComplex (u : ℂ)) (iteratedDeriv 3 kernelComplex (u : ℂ))
    (iteratedDeriv 4 kernelComplex (u : ℂ)) B he (hp 1 (Or.inl rfl))
    (hp 2 (Or.inr rfl)) hk0 (hk 1 (by norm_num)) (hk 2 (by norm_num))
    (hk 3 (by norm_num)) (hk 4 (by norm_num))
  exact h.trans_eq (by dsimp [C,D]; ring)

theorem regularFourth_uniform_integral_bound (t : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ a : ℝ, 1 < a → a ≤ 5/4 →
      (∫ u : ℝ in Ioo 0 1, ‖regularFourth a t (u : ℂ)‖) ≤ M := by
  obtain ⟨C,D,hC,hD,hbound⟩ := regularFourth_uniform_pointwise t
  refine ⟨C*(6*|t|)+D,by positivity,?_⟩
  intro a ha ha5
  have hp := (phaseJet_integrable_near a t 3 (by norm_num; linarith) 1 (by norm_num)).norm
  have hd : IntegrableOn (fun _ : ℝ => D) (Ioo 0 1) :=
    (show IntegrableOn (fun _ : ℝ => D) (Icc 0 1) from
      continuousOn_const.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hr := (regularFourth_integrable_near a t ha 1 (by norm_num)).norm
  calc
    _ ≤ ∫ u : ℝ in Ioo 0 1, C*‖phaseJet a t 3 (u : ℂ)‖+D := by
      apply integral_mono_ae hr ((hp.const_mul C).add hd)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact hbound a ha.le ha5 u ⟨hu.1.le,hu.2.le⟩
    _ = C*(∫ u : ℝ in Ioo 0 1, ‖phaseJet a t 3 (u : ℂ)‖)+D := by
      rw [integral_add (hp.const_mul C) hd,integral_const_mul]
      simp
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      (phase_three_integral_norm_bound a t ha ha5) hC) le_rfl

theorem cutoff_uniform_norm_integral_bound (t : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ a : ℝ, 1 < a → a ≤ 5/4 → (∫ u : ℝ in Ioi 0, ‖cutoff a t u‖) ≤ M := by
  have hc : ContinuousOn (fun a : ℝ => RiemannRealOrderCutoffBoundary.mass a t)
      (Icc 1 (5/4)) := by
    intro a ha
    exact (RiemannRealOrderUniformCutoff.mass_continuousAt a t (by linarith [ha.1])).continuousWithinAt
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro a ha ha5
  rw [RiemannRealOrderCutoffBoundary.cutoff_norm_integral a t ha]
  exact (show |RiemannRealOrderCutoffBoundary.mass a t| ≤ M from
    (hM a ⟨ha.le,ha5⟩)).trans (le_max_left _ _)

theorem remainder_derivative_uniform_near (t : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ a : ℝ, 1 < a → a ≤ 5/4 →
      (∫ u : ℝ in Ioo 0 1, ‖deriv (remainder a t) u‖) ≤ M := by
  obtain ⟨C,hC,hcritical⟩ := singular_fourth_uniform_integral_bound t
  obtain ⟨D,hD,hregular⟩ := regularFourth_uniform_integral_bound t
  obtain ⟨Q,hQ,hcutoff⟩ := cutoff_uniform_norm_integral_bound t
  refine ⟨C+Q+D,by positivity,?_⟩
  intro a ha ha5
  obtain ⟨hi,hI⟩ := hcritical a ha ha5
  have hqfull : IntegrableOn (fun u : ℝ => ‖cutoff a t u‖) (Ioi 0) :=
    (cutoff_integrable a t ha).norm
  have hq := hqfull.mono_set (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hu => hu.1)
  have hr := (regularFourth_integrable_near a t ha 1 (by norm_num)).norm
  have hd := ((remainder_derivative_integrable a t ha (by linarith)).mono_set
    (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hu => hu.1)).norm
  have hqi : (∫ u : ℝ in Ioo 0 1, ‖cutoff a t u‖) ≤ Q := by
    apply le_trans _ (hcutoff a ha ha5)
    exact setIntegral_mono_set hqfull (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun u hu => hu.1)
  calc
    _ ≤ ∫ u : ℝ in Ioo 0 1,
        ‖phaseJet a t 4 (u : ℂ)*endpointDifference a t u‖+
          ‖cutoff a t u‖+‖regularFourth a t (u : ℂ)‖ := by
      apply integral_mono_ae hd ((hi.norm.add hq).add hr)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      rw [remainder_derivative_eq a t u hu.1]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (∫ u : ℝ in Ioo 0 1, ‖phaseJet a t 4 (u : ℂ)*endpointDifference a t u‖)+
        (∫ u : ℝ in Ioo 0 1, ‖cutoff a t u‖)+
          (∫ u : ℝ in Ioo 0 1, ‖regularFourth a t (u : ℂ)‖) := by
      exact (integral_add (hi.norm.add hq) hr).trans
        (congrArg (fun z : ℝ => z+(∫ u : ℝ in Ioo 0 1, ‖regularFourth a t (u : ℂ)‖))
          (integral_add hi.norm hq))
    _ ≤ _ := add_le_add (add_le_add hI hqi) (hregular a ha ha5)

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderUniformRegular
