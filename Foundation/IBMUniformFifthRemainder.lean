import Foundation.IBMUniformQuarticVariation
import Foundation.IBMFourthTaylor

/-! Vanishing higher-order errors along the actual continuous reflected-clock IBM.
The quartic variation is used only in its proved probability topology. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformFifthRemainder
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMUniformQuarticFamily IBMUniformQuarticVariation
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.sceneryPath
  IBMConstructedSources.ibmValue

def mesh (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => |ibmValue (grid (T / (n + 1)) (k + 1)) ω -
      ibmValue (grid (T / (n + 1)) k) ω|)

theorem mesh_nonneg (T : ℝ≥0) (n : ℕ) (ω : JointSample) : 0 ≤ mesh T n ω :=
  (abs_nonneg _).trans (Finset.le_sup' (fun k =>
    |ibmValue (grid (T / (n + 1)) (k + 1)) ω - ibmValue (grid (T / (n + 1)) k) ω|)
    (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

theorem mesh_measurable (T : ℝ≥0) (n : ℕ) : Measurable (mesh T n) := by
  apply Finset.measurable_range_sup''
  intro k hk
  exact continuous_abs.measurable.comp
    ((ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)).sub
    (ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)))

/-- Every sample has vanishing mesh increments; no probabilistic regularity
upgrade is inferred from quartic convergence. -/
theorem mesh_tendsto (T : ℝ≥0) (ω : JointSample) :
    Tendsto (fun n => mesh T n ω) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (mesh_nonneg T n ω)
  · intro ε hε
    obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp
      ((isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).uniformContinuousOn_of_continuous
        (ibmValue_continuous ω).continuousOn) ε hε
    have hstep : Tendsto (fun n : ℕ => (T : ℝ) / (n+1 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_right _ _
        tendsto_natCast_atTop_atTop)
    filter_upwards [hstep.eventually (gt_mem_nhds hδ)] with n hn
    apply (Finset.sup'_lt_iff _).mpr
    intro k hk
    have hkn : k+1 ≤ n+1 := Finset.mem_range.mp hk
    have hp : 0 < (n+1 : ℝ) := by positivity
    have hT : 0 ≤ (T : ℝ) := T.coe_nonneg
    have hmem (j : ℕ) (hj : j ≤ n+1) : grid (T / (n + 1)) j ∈ Icc 0 T := by
      constructor
      · exact zero_le
      · apply NNReal.coe_le_coe.mp
        simp only [grid, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast]
        calc
          (T : ℝ) / (n + 1) * j ≤ (T : ℝ) / (n + 1) * (n + 1) := by
            gcongr
            exact_mod_cast hj
          _ = T := div_mul_cancel₀ _ hp.ne'
    have hd : dist (grid (T / (n + 1)) (k + 1)) (grid (T / (n + 1)) k) < δ := by
      rw [NNReal.dist_eq]
      simp only [grid, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
        Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
      have he : (T : ℝ) / (n + 1) * (k + 1) - (T : ℝ) / (n + 1) * k =
          (T : ℝ) / (n + 1) := by ring
      rw [he, abs_of_nonneg (div_nonneg hT hp.le)]
      exact hn
    simpa only [Real.dist_eq] using hu _ (hmem _ hkn) _ (hmem _ (by omega)) hd

theorem mesh_tendstoInMeasure (T : ℝ≥0) :
    TendstoInMeasure jointMeasure (mesh T) atTop (fun _ => (0 : ℝ)) :=
  tendstoInMeasure_of_tendsto_ae (fun n => (mesh_measurable T n).aestronglyMeasurable)
    (ae_of_all _ (mesh_tendsto T))

def fifth (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    |ibmValue (grid (T / (n + 1)) (k + 1)) ω - ibmValue (grid (T / (n + 1)) k) ω| ^ 5

theorem fifth_nonneg (T : ℝ≥0) (n : ℕ) (ω : JointSample) : 0 ≤ fifth T n ω :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem fifth_le (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    fifth T n ω ≤ mesh T n ω * quartic T (n + 1) ω := by
  rw [quartic, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have h := Finset.le_sup' (fun k =>
    |ibmValue (grid (T / (n + 1)) (k + 1)) ω - ibmValue (grid (T / (n + 1)) k) ω|) hk
  change |ibmValue (grid (T / (n + 1)) (k + 1)) ω -
    ibmValue (grid (T / (n + 1)) k) ω| ≤ mesh T n ω at h
  simp only [IBMUniformQuarticFamily.segment, Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  simp only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left h
    (sq_nonneg ((ibmValue (grid (T / (n + 1)) (k + 1)) ω -
      ibmValue (grid (T / (n + 1)) k) ω) ^ 2))

/-- A proved tightness argument, using only the actual quartic probability
limit and the pathwise vanishing mesh. No joint L2 bound is needed. -/
theorem dominated_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T)
    (E : ℕ → JointSample → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ n ω, |E n ω| ≤ C * mesh T n ω * quartic T (n + 1) ω) :
    TendstoInMeasure jointMeasure E atTop (fun _ => (0 : ℝ)) := by
  have hm := tendstoInMeasure_iff_measureReal_norm.mp (mesh_tendstoInMeasure T)
  have hq := tendstoInMeasure_iff_measureReal_norm.mp (quartic_tendstoInMeasure hT)
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  let K : ℝ := C * (3 * (T : ℝ) + 1) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have he : 0 < ε / K := div_pos hε hK
  have hb (n : ℕ) : jointMeasure.real {ω | ε ≤ |E n ω|} ≤
      jointMeasure.real {ω | ε / K ≤ |mesh T n ω|} +
      jointMeasure.real {ω | 1 ≤ |quartic T (n + 1) ω - 3 * (T : ℝ)|} := by
    apply le_trans (measureReal_mono (μ := jointMeasure) (s₂ :=
      {ω | ε / K ≤ |mesh T n ω|} ∪
      {ω | 1 ≤ |quartic T (n + 1) ω - 3 * (T : ℝ)|}) ?_ (by finiteness))
      (measureReal_union_le _ _)
    intro ω hω
    by_contra hn
    have hm' : mesh T n ω < ε / K := by
      have : ¬ ε / K ≤ |mesh T n ω| := fun h => hn (Or.inl h)
      simpa [abs_of_nonneg (mesh_nonneg T n ω)] using lt_of_not_ge this
    have hq' : quartic T (n + 1) ω ≤ 3 * (T : ℝ) + 1 := by
      have : |quartic T (n + 1) ω - 3 * (T : ℝ)| < 1 :=
        lt_of_not_ge fun h => hn (Or.inr h)
      linarith [(le_abs_self (quartic T (n + 1) ω - 3 * (T : ℝ)))]
    have hc : 0 ≤ C * mesh T n ω := mul_nonneg hC (mesh_nonneg T n ω)
    have hbound := (hE n ω).trans (mul_le_mul_of_nonneg_left hq' hc)
    have hsmall : mesh T n ω * K < ε := (lt_div_iff₀ hK).mp hm'
    have hcomp : C * mesh T n ω * (3 * (T : ℝ) + 1) ≤ mesh T n ω * K := by
      dsimp [K]
      nlinarith [mesh_nonneg T n ω]
    change ε ≤ |E n ω| at hω
    exact (not_lt_of_ge hω) ((hbound.trans hcomp).trans_lt hsmall)
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  simpa only [sub_zero, Real.norm_eq_abs, add_zero] using (hm (ε / K) he).add (hq 1 zero_lt_one)

theorem fifth_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (fifth T) atTop (fun _ => (0 : ℝ)) := by
  apply dominated_tendstoInMeasure hT _ (C := 1) zero_le_one
  intro n ω
  simpa only [abs_of_nonneg (fifth_nonneg T n ω), one_mul] using fifth_le T n ω

def remainderSum (f : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), IBMFourthTaylor.remainder f
    (ibmValue (grid (T / (n + 1)) k) ω) (ibmValue (grid (T / (n + 1)) (k + 1)) ω)

theorem remainderSum_le (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    |remainderSum f T n ω| ≤ (M / 120) * fifth T n ω := by
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), |IBMFourthTaylor.remainder f
        (ibmValue (grid (T / (n + 1)) k) ω)
        (ibmValue (grid (T / (n + 1)) (k + 1)) ω)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      rw [fifth, Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => IBMFourthTaylor.remainder_bound f hf M hM _ _

/-- The genuine sum of fourth-order Taylor remainders along actual IBM
vanishes in probability, on the stated C5 bounded-fifth-derivative domain. -/
theorem remainderSum_tendstoInMeasure (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (remainderSum f T) atTop (fun _ => (0 : ℝ)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hc : 0 ≤ M / 120 := by positivity
  apply dominated_tendstoInMeasure hT _ hc
  intro n ω
  exact (remainderSum_le f hf M hM T n ω).trans
    ((mul_le_mul_of_nonneg_left (fifth_le T n ω) hc).trans_eq (by ring))

def absoluteRemainderSum (f : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), |IBMFourthTaylor.remainder f
    (ibmValue (grid (T / (n + 1)) k) ω) (ibmValue (grid (T / (n + 1)) (k + 1)) ω)|

/-- Total absolute Taylor error, not just a cancellation of signed errors. -/
theorem absoluteRemainderSum_le (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    |absoluteRemainderSum f T n ω| ≤ (M / 120) * fifth T n ω := by
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))]
  rw [fifth, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => IBMFourthTaylor.remainder_bound f hf M hM _ _

theorem absoluteRemainderSum_tendstoInMeasure (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (absoluteRemainderSum f T) atTop (fun _ => (0 : ℝ)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hc : 0 ≤ M / 120 := by positivity
  apply dominated_tendstoInMeasure hT _ hc
  intro n ω
  exact (absoluteRemainderSum_le f hf M hM T n ω).trans
    ((mul_le_mul_of_nonneg_left (fifth_le T n ω) hc).trans_eq (by ring))

end OperatorDerivativeRewrite.Foundation.IBMUniformFifthRemainder
