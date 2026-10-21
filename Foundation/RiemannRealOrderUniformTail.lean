import Foundation.RiemannRealOrderUniformRegular
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Common fourth-density and cutoff-derivative bounds away from zero. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderUniformTail
open RiemannThetaComplexKernel RiemannRealOrderFractionalJets
open RiemannRealOrderFractionalRemainder RiemannRealOrderFractionalDensity
open RiemannRealOrderUniformEndpoint RiemannRealOrderUniformRegular

private theorem phase_joint_continuousAt (n : ℕ) (t : ℝ) (p : ℝ × ℝ) (hp : 0 < p.2) :
    ContinuousAt (fun q : ℝ × ℝ => phaseJet q.1 t n (q.2 : ℂ)) p := by
  have hf : ContinuousAt (fun q : ℝ × ℝ => (falling (2*q.1) n : ℂ)) p := by
    unfold falling
    fun_prop
  have hb : ContinuousAt (fun q : ℝ × ℝ => (q.2 : ℂ)) p := by fun_prop
  have he : ContinuousAt (fun q : ℝ × ℝ => ((2*q.1-(n : ℝ) : ℝ) : ℂ)) p := by fun_prop
  exact continuousAt_const.mul (hf.mul (hb.cpow he (Complex.mem_slitPlane_iff.mpr (Or.inl hp))))

private theorem exponential_joint_continuousAt (t : ℝ) (p : ℝ × ℝ) (hp : 0 < p.2) :
    ContinuousAt (fun q : ℝ × ℝ => exponential q.1 t (q.2 : ℂ)) p := by
  have h := (phase_joint_continuousAt 0 t p hp).cexp
  simpa only [phaseJet,powerJet_zero,exponential] using h

theorem density_fourth_joint_continuousAt (t : ℝ) (p : ℝ × ℝ) (hp : 0 < p.2) :
    ContinuousAt (fun q : ℝ × ℝ => iteratedDeriv 4 (density q.1 t) (q.2 : ℂ)) p := by
  let f : ℝ × ℝ → ℂ := fun q => exponential q.1 t (q.2 : ℂ)*
    (iteratedDeriv 4 kernelComplex (q.2 : ℂ)+
      4*phaseJet q.1 t 1 (q.2 : ℂ)*iteratedDeriv 3 kernelComplex (q.2 : ℂ)+
      6*(phaseJet q.1 t 2 (q.2 : ℂ)+(phaseJet q.1 t 1 (q.2 : ℂ))^2)*
        iteratedDeriv 2 kernelComplex (q.2 : ℂ)+
      4*(phaseJet q.1 t 3 (q.2 : ℂ)+3*phaseJet q.1 t 1 (q.2 : ℂ)*
        phaseJet q.1 t 2 (q.2 : ℂ)+(phaseJet q.1 t 1 (q.2 : ℂ))^3)*
          iteratedDeriv 1 kernelComplex (q.2 : ℂ)+
      (phaseJet q.1 t 4 (q.2 : ℂ)+4*phaseJet q.1 t 1 (q.2 : ℂ)*phaseJet q.1 t 3 (q.2 : ℂ)+
        3*(phaseJet q.1 t 2 (q.2 : ℂ))^2+6*(phaseJet q.1 t 1 (q.2 : ℂ))^2*
          phaseJet q.1 t 2 (q.2 : ℂ)+(phaseJet q.1 t 1 (q.2 : ℂ))^4)*kernelComplex (q.2 : ℂ))
  have he := exponential_joint_continuousAt t p hp
  have hphase (n : ℕ) := phase_joint_continuousAt n t p hp
  have hk (n : ℕ) : ContinuousAt (fun q : ℝ × ℝ => iteratedDeriv n kernelComplex (q.2 : ℂ)) p :=
    (kernel_derivative_continuous n).continuousAt.comp continuousAt_snd
  have hkc : ContinuousAt (fun q : ℝ × ℝ => kernelComplex (q.2 : ℂ)) p := by
    simpa only [iteratedDeriv_zero] using hk 0
  have hf : ContinuousAt f p := by dsimp only [f]; fun_prop
  apply hf.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hp)] with q hq
  exact density_fourth_derivative q.1 t (q.2 : ℂ)
    (Complex.mem_slitPlane_iff.mpr (Or.inl hq))
    (by simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im] using Real.exp_pos (4*q.2))

theorem density_fourth_uniform_compact_bound (t : ℝ) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ a : ℝ, 1 ≤ a → a ≤ 5/4 → ∀ u ∈ Icc (1 : ℝ) 2,
      ‖iteratedDeriv 4 (density a t) (u : ℂ)‖ ≤ B := by
  have hc : ContinuousOn (fun q : ℝ × ℝ => iteratedDeriv 4 (density q.1 t) (q.2 : ℂ))
      (Icc 1 (5/4) ×ˢ Icc 1 2) := by
    intro p hp
    exact (density_fourth_joint_continuousAt t p (by linarith [hp.2.1])).continuousWithinAt
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro a ha ha5 u hu
  exact (hB (a,u) ⟨⟨ha,ha5⟩,hu⟩).trans (le_max_left _ _)

theorem density_fourth_uniform_integral_away (t : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ a : ℝ, 1 ≤ a → a ≤ 5/4 →
      (∫ u : ℝ in Ici 1, ‖iteratedDeriv 4 (density a t) (u : ℂ)‖) ≤ M := by
  obtain ⟨B,hB,hbound⟩ := density_fourth_uniform_compact_bound t
  refine ⟨B+|∫ u : ℝ in Ici 2, tailMajorant 4 t u|,by positivity,?_⟩
  intro a ha ha5
  have hi : IntegrableOn (fun u : ℝ => ‖iteratedDeriv 4 (density a t) (u : ℂ)‖) (Ici 1) :=
    (density_iteratedDeriv_integrable_away_zero 4 a t 1 (by linarith)
      (by linarith) (by norm_num)).norm
  have hc := hi.mono_set (show Ico (1 : ℝ) 2 ⊆ Ici 1 from fun _ hu => hu.1)
  have ht := hi.mono_set (Ici_subset_Ici.mpr (by norm_num : (1 : ℝ) ≤ 2))
  have hb : IntegrableOn (fun _ : ℝ => B) (Ico 1 2) :=
    (show IntegrableOn (fun _ : ℝ => B) (Icc 1 2) from
      continuousOn_const.integrableOn_Icc).mono_set Ico_subset_Icc_self
  have hci : (∫ u : ℝ in Ico 1 2, ‖iteratedDeriv 4 (density a t) (u : ℂ)‖) ≤ B := by
    calc
      _ ≤ ∫ _u : ℝ in Ico 1 2, B := by
        apply integral_mono_ae hc hb
        filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
        exact hbound a ha ha5 u ⟨hu.1,hu.2.le⟩
      _ = _ := by simp; ring
  have hti : (∫ u : ℝ in Ici 2, ‖iteratedDeriv 4 (density a t) (u : ℂ)‖) ≤
      ∫ u : ℝ in Ici 2, tailMajorant 4 t u := by
    apply integral_mono_ae ht (tailMajorant_integrable 4 t)
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact density_iteratedDeriv_bound 4 a t u (by linarith) (by linarith) hu
  have hdis : Disjoint (Ico (1 : ℝ) 2) (Ici 2) := by
    rw [Set.disjoint_left]
    intro u hu hv
    exact not_lt_of_ge hv hu.2
  have hunion : Ico (1 : ℝ) 2 ∪ Ici 2=Ici 1 := by
    ext u
    constructor
    · rintro (h | h)
      · exact h.1
      · exact le_trans (by norm_num : (1 : ℝ) ≤ 2) h
    · intro h
      by_cases hu : u < 2
      · exact Or.inl ⟨h,hu⟩
      · exact Or.inr (le_of_not_gt hu)
  rw [← hunion,setIntegral_union hdis measurableSet_Ici hc ht]
  exact add_le_add hci (hti.trans (le_abs_self _))

theorem cutoff_derivative_uniform_bound (a t u : ℝ) (ha : 1 ≤ a) (ha5 : a ≤ 5/4)
    (hu : 1 ≤ u) :
    ‖deriv (cutoff a t) u‖ ≤ 6*|t| * ‖kernelComplex 0‖*Real.exp (-u) := by
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hp3 : ‖phaseJet a t 3 (u : ℂ)‖ ≤ 3*|t| := by
    calc
      _ ≤ 6*|t| * (2*a-2)*u^(2*a-3) := phase_three_norm_bound a t u ha ha5 hu0
      _ ≤ 6*|t| * (2*a-2)*1 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith))
          (mul_nonneg (by positivity) (by linarith))
      _ ≤ _ := by nlinarith [abs_nonneg t]
  have hp4 : ‖phaseJet a t 4 (u : ℂ)‖ ≤ 3*|t| := by
    calc
      _ ≤ 6*|t| * (2*a-2)*u^(2*a-4) := phase_four_norm_bound a t u ha ha5 hu0
      _ ≤ 6*|t| * (2*a-2)*1 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith))
          (mul_nonneg (by positivity) (by linarith))
      _ ≤ _ := by nlinarith [abs_nonneg t]
  have hp : ‖phaseJet a t 4 (u : ℂ)-phaseJet a t 3 (u : ℂ)‖ ≤ 6*|t| :=
    (norm_sub_le _ _).trans (by linarith)
  rw [(cutoff_hasDerivAt a t u hu0).deriv,norm_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) (Real.exp_pos _).le

theorem cutoff_derivative_uniform_integral_away (t : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ a : ℝ, 1 ≤ a → a ≤ 5/4 →
      (∫ u : ℝ in Ici 1, ‖deriv (cutoff a t) u‖) ≤ M := by
  let C : ℝ := 6*|t| * ‖kernelComplex 0‖
  have hi : IntegrableOn (fun u : ℝ => C*Real.exp (-u)) (Ici 1) :=
    (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_neg_Ioi 1)).const_mul C
  refine ⟨|∫ u : ℝ in Ici 1, C*Real.exp (-u)|,abs_nonneg _,?_⟩
  intro a ha ha5
  have hq : IntegrableOn (deriv (cutoff a t)) (Ici 1) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (cutoff_derivative_integrable_away a t 1 (by norm_num))
  apply le_trans _ (le_abs_self _)
  apply integral_mono_ae hq.norm hi
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  exact cutoff_derivative_uniform_bound a t u ha ha5 hu

theorem remainder_derivative_uniform_away (t : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ a : ℝ, 1 < a → a ≤ 5/4 →
      (∫ u : ℝ in Ici 1, ‖deriv (remainder a t) u‖) ≤ M := by
  obtain ⟨D,hD,hd⟩ := density_fourth_uniform_integral_away t
  obtain ⟨Q,hQ,hq⟩ := cutoff_derivative_uniform_integral_away t
  refine ⟨D+Q,by positivity,?_⟩
  intro a ha ha5
  have hdint := (density_iteratedDeriv_integrable_away_zero 4 a t 1 (by linarith)
    (by linarith) (by norm_num)).norm
  have hqint := (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
    (cutoff_derivative_integrable_away a t 1 (by norm_num))).norm
  have hrint := ((remainder_derivative_integrable a t ha (by linarith)).mono_set
    (show Ici (1 : ℝ) ⊆ Ioi 0 from fun u hu =>
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hu)).norm
  calc
    _ ≤ ∫ u : ℝ in Ici 1, ‖iteratedDeriv 4 (density a t) (u : ℂ)‖+‖deriv (cutoff a t) u‖ := by
      apply integral_mono_ae hrint (hdint.add hqint)
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
      dsimp only [Pi.add_apply]
      rw [(remainder_hasDerivAt a t u hu0).deriv,(cutoff_hasDerivAt a t u hu0).deriv]
      exact norm_sub_le _ _
    _ = (∫ u : ℝ in Ici 1, ‖iteratedDeriv 4 (density a t) (u : ℂ)‖)+
        (∫ u : ℝ in Ici 1, ‖deriv (cutoff a t) u‖) := integral_add hdint hqint
    _ ≤ _ := add_le_add (hd a ha.le ha5) (hq a ha.le ha5)

theorem remainder_derivative_uniform_integral (t : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ a : ℝ, 1 < a → a ≤ 5/4 →
      (∫ u : ℝ in Ioi 0, ‖deriv (remainder a t) u‖) ≤ M := by
  obtain ⟨N,hN,hn⟩ := remainder_derivative_uniform_near t
  obtain ⟨T,hT,ht⟩ := remainder_derivative_uniform_away t
  refine ⟨N+T,by positivity,?_⟩
  intro a ha ha5
  have hi : IntegrableOn (fun u : ℝ => ‖deriv (remainder a t) u‖) (Ioi 0) :=
    (remainder_derivative_integrable a t ha (by linarith)).norm
  have hnear := hi.mono_set (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hu => hu.1)
  have htail := hi.mono_set
    (show Ici (1 : ℝ) ⊆ Ioi 0 from fun u hu =>
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hu)
  have hdis : Disjoint (Ioo (0 : ℝ) 1) (Ici 1) := by
    rw [Set.disjoint_left]
    intro u hu hv
    exact not_lt_of_ge hv hu.2
  have hunion : Ioo (0 : ℝ) 1 ∪ Ici 1=Ioi 0 := by
    ext u
    constructor
    · rintro (h | h)
      · exact h.1
      · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h
    · intro h
      by_cases hu : u < 1
      · exact Or.inl ⟨h,hu⟩
      · exact Or.inr (le_of_not_gt hu)
  rw [← hunion,setIntegral_union hdis measurableSet_Ici hnear htail]
  exact add_le_add (hn a ha ha5) (ht a ha ha5)

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderUniformTail
