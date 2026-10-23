import Foundation.IBMActualSimpson

/-! Uniform-in-grid-prefix signed Simpson integration of actual IBM.
Targets are genuine oriented integrals at the corresponding actual endpoints. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformSimpsonProcess
open IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMUniformQuarticFamily IBMUniformFifthRemainder IBMActualSimpson
attribute [local irreducible] IBMConstructedSources.clockPath IBMConstructedSources.ibmValue

theorem integral_continuous (g : ℝ → ℝ) (hg : Continuous g) (ω : JointSample) :
    Continuous (fun t => lineIntegral g t ω) := by
  have hp : Continuous (primitive g) :=
    (intervalIntegral.differentiable_integral_of_continuous hg).continuous
  have he : (fun t => lineIntegral g t ω) = fun t =>
      primitive g (ibmValue t ω) - primitive g (ibmValue 0 ω) :=
    funext fun t => lineIntegral_eq_primitive g hg t ω
  rw [he]
  exact (hp.comp (ibmValue_continuous ω)).sub continuous_const

theorem integral_jointly_measurable (g : ℝ → ℝ) (hg : Continuous g) :
    Measurable (fun p : ℝ≥0 × JointSample => lineIntegral g p.1 p.2) := by
  have hp : Continuous (primitive g) :=
    (intervalIntegral.differentiable_integral_of_continuous hg).continuous
  have he : (fun p : ℝ≥0 × JointSample => lineIntegral g p.1 p.2) = fun p =>
      primitive g (ibmValue p.1 p.2) - primitive g (ibmValue 0 p.2) :=
    funext fun p => lineIntegral_eq_primitive g hg p.1 p.2
  rw [he]
  exact (hp.measurable.comp ibmValue_jointly_measurable).sub
    (hp.measurable.comp (ibmValue_jointly_measurable.comp
      (measurable_const.prodMk measurable_snd)))

def integralPath (g : ℝ → ℝ) (hg : Continuous g) (ω : JointSample) : C(ℝ≥0, ℝ) :=
  ⟨fun t => lineIntegral g t ω, integral_continuous g hg ω⟩

theorem integralPath_measurable (g : ℝ → ℝ) (hg : Continuous g) :
    Measurable (integralPath g hg) :=
  ContinuousMap.measurable_iff_eval.mpr (lineIntegral_measurable g hg)

def prefixSums (g : ℝ → ℝ) (T : ℝ≥0) (n m : ℕ) (ω : JointSample) : ℝ :=
  ∑ i ∈ Finset.range m, IBMSimpsonPeano.simpson g
    (ibmValue (grid (T / (n + 1)) i) ω) (ibmValue (grid (T / (n + 1)) (i + 1)) ω)

def error (g : ℝ → ℝ) (T : ℝ≥0) (n m : ℕ) (ω : JointSample) : ℝ :=
  prefixSums g T n m ω - lineIntegral g (grid (T / (n + 1)) m) ω

def maximum (g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) : ℝ :=
  (Finset.range (n + 2)).sup' Finset.nonempty_range_add_one (fun m => |error g T n m ω|)

theorem prefixSums_measurable (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) (n m : ℕ) :
    Measurable (prefixSums g T n m) := by
  have hc : Continuous (fun p : ℝ × ℝ => IBMSimpsonPeano.simpson g p.1 p.2) := by
    unfold IBMSimpsonPeano.simpson
    fun_prop
  have hm (r : ℝ≥0) : Measurable (ibmValue r) :=
    ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  unfold prefixSums
  apply Finset.measurable_sum
  intro i hi
  exact hc.measurable.comp
    ((hm (grid (T / (n + 1)) i)).prodMk (hm (grid (T / (n + 1)) (i + 1))))

theorem error_measurable (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) (n m : ℕ) :
    Measurable (error g T n m) :=
  (prefixSums_measurable g hg T n m).sub (lineIntegral_measurable g hg _)

theorem maximum_nonneg (g : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    0 ≤ maximum g T n ω :=
  (abs_nonneg _).trans (Finset.le_sup' (fun m => |error g T n m ω|)
    (b := 0) (by simp))

theorem maximum_measurable (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) (n : ℕ) :
    Measurable (maximum g T n) := by
  apply Finset.measurable_range_sup''
  intro m hm
  exact continuous_abs.measurable.comp (error_measurable g hg T n m)

theorem error_le_maximum (g : ℝ → ℝ) (T : ℝ≥0) (n m : ℕ) (hm : m ≤ n + 1)
    (ω : JointSample) : |error g T n m ω| ≤ maximum g T n ω :=
  Finset.le_sup' (fun k => |error g T n k ω|) (Finset.mem_range.mpr (by omega))

theorem finite_error_identity (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0)
    (n m : ℕ) (ω : JointSample) :
    error g T n m ω = ∑ i ∈ Finset.range m,
      (IBMSimpsonPeano.simpson g (ibmValue (grid (T / (n + 1)) i) ω)
        (ibmValue (grid (T / (n + 1)) (i + 1)) ω) -
        (primitive g (ibmValue (grid (T / (n + 1)) (i + 1)) ω) -
          primitive g (ibmValue (grid (T / (n + 1)) i) ω))) := by
  have ht := Finset.sum_range_sub
    (fun i => primitive g (ibmValue (grid (T / (n + 1)) i) ω)) m
  have hz : grid (T / (n + 1)) 0 = 0 := by simp [grid]
  rw [hz] at ht
  unfold error prefixSums
  rw [lineIntegral_eq_primitive g hg, ← ht, ← Finset.sum_sub_distrib]

/-- One compact modulus controls ALL prefixes of the increasing grid,
including the empty prefix. No union bound growing with the grid is used. -/
theorem maximum_eventual_bound (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (T : ℝ≥0)
    (ω : JointSample) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, maximum g T n ω ≤ ε * quartic T (n + 1) ω := by
  let R := IBMContinuousBlockWeights.pathBound id continuous_id T ω
  obtain ⟨δ, hδ, hu⟩ := IBMSimpsonPeano.compact_error_bound (primitive g)
    (primitive_contDiff g hg) R ε hε
  rw [primitive_deriv g hg.continuous] at hu
  filter_upwards [(mesh_tendsto T ω).eventually (gt_mem_nhds hδ)] with n hn
  apply Finset.sup'_le
  intro m hm
  have hmN : m ≤ n + 1 := by have := Finset.mem_range.mp hm; omega
  rw [finite_error_identity g hg.continuous]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply le_trans (b := ε * ∑ i ∈ Finset.range m,
    (ibmValue (grid (T / (n + 1)) (i + 1)) ω -
      ibmValue (grid (T / (n + 1)) i) ω)^4)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hiN : i + 1 ≤ n + 1 := (Finset.mem_range.mp hi).trans_le hmN
    have hb (j : ℕ) (hj : j ≤ n + 1) : |ibmValue (grid (T / (n + 1)) j) ω| ≤ R :=
      IBMContinuousBlockWeights.pathBound_bound id continuous_id T ω _
        (IBMActualPeanoRemainder.grid_le T n j hj)
    have hd : |ibmValue (grid (T / (n + 1)) (i + 1)) ω -
        ibmValue (grid (T / (n + 1)) i) ω| ≤ mesh T n ω :=
      Finset.le_sup' (fun k => |ibmValue (grid (T / (n + 1)) (k + 1)) ω -
        ibmValue (grid (T / (n + 1)) k) ω|) (Finset.mem_range.mpr (by omega))
    have h := hu (ibmValue (grid (T / (n + 1)) i) ω)
      (ibmValue (grid (T / (n + 1)) (i + 1)) ω)
      (hb i (by omega)) (hb (i + 1) hiN) (hd.trans_lt hn)
    simpa only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using h
  · apply mul_le_mul_of_nonneg_left _ hε.le
    unfold quartic
    simp only [IBMUniformQuarticFamily.segment, Nat.cast_add, Nat.cast_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmN)
      (fun _ _ _ => by positivity)

/-- Uniform convergence in probability over EVERY grid prefix, for all
global C3 one-forms and the original actual IBM joint law. -/
theorem maximum_tendstoInMeasure (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g)
    {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (maximum g T) atTop (fun _ => (0 : ℝ)) := by
  apply quartic_peano_tendstoInMeasure hT _ (maximum_measurable g hg.continuous T)
  intro ω ε hε
  simpa only [abs_of_nonneg (maximum_nonneg g T _ ω)] using
    maximum_eventual_bound g hg T ω hε

theorem selected_measurable (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) (n : ℕ)
    (m : JointSample → ℕ) (hm : Measurable m) :
    Measurable (fun ω => error g T n (m ω) ω) := by
  have hp : Measurable (fun p : ℕ × JointSample => error g T n p.1 p.2) :=
    measurable_from_prod_countable_right
      (f := fun p : ℕ × JointSample => error g T n p.1 p.2)
      (fun k => error_measurable g hg T n k)
  exact hp.comp (hm.prodMk measurable_id)

theorem selected_sums_measurable (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) (n : ℕ)
    (m : JointSample → ℕ) (hm : Measurable m) :
    Measurable (fun ω => prefixSums g T n (m ω) ω) := by
  have hp : Measurable (fun p : ℕ × JointSample => prefixSums g T n p.1 p.2) :=
    measurable_from_prod_countable_right
      (f := fun p : ℕ × JointSample => prefixSums g T n p.1 p.2)
      (fun k => prefixSums_measurable g hg T n k)
  exact hp.comp (hm.prodMk measurable_id)

/-- Sample-dependent grid endpoints are controlled by the SAME maximum.
Measurable selectors give ordinary measurable stochastic approximants;
no stopping-time or optional-sampling hypothesis is asserted. -/
theorem selected_error_tendstoInMeasure (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g)
    {T : ℝ≥0} (hT : 0 < T) (m : ℕ → JointSample → ℕ)
    (hm : ∀ n ω, m n ω ≤ n + 1) :
    TendstoInMeasure jointMeasure (fun n ω => error g T n (m n ω) ω)
      atTop (fun _ => (0 : ℝ)) := by
  have h := tendstoInMeasure_iff_measureReal_norm.mp (maximum_tendstoInMeasure g hg hT)
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have hb (n : ℕ) : jointMeasure.real {ω | ε ≤ |error g T n (m n ω) ω|} ≤
      jointMeasure.real {ω | ε ≤ maximum g T n ω} := by
    apply measureReal_mono (μ := jointMeasure) (h₂ := measure_ne_top _ _)
    intro ω hω
    exact hω.trans (error_le_maximum g T n (m n ω) (hm n ω) ω)
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg (maximum_nonneg g T _ _)] using h ε hε

end OperatorDerivativeRewrite.Foundation.IBMUniformSimpsonProcess
