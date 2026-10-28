import Foundation.SU2EventMixing

/-! Stationary two-time event laws for the explicit SU(2) loop kernel. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.SU2InteractingLoopKernel
open OperatorDerivativeRewrite.Foundation.SU2LoopEquilibrium
open OperatorDerivativeRewrite.Foundation.SU2ResidualEntropy
open OperatorDerivativeRewrite.Foundation.SU2EventMixing

namespace OperatorDerivativeRewrite.Foundation.SU2LagEventCorrelation

def lagKernel (r : ℝ) : ℕ → Kernel SU2 SU2
  | 0 => Kernel.id
  | n + 1 => loopKernel r ∘ₖ lagKernel r n

theorem lagKernel_markov (r : ℝ) (n : ℕ) : IsMarkovKernel (lagKernel r n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel SU2 SU2); infer_instance
  | succ n ih =>
      letI : IsMarkovKernel (lagKernel r n) := ih
      letI : IsMarkovKernel (loopKernel r) := loopKernel_markov r
      change IsMarkovKernel (loopKernel r ∘ₖ lagKernel r n)
      infer_instance

theorem lagKernel_apply (r : ℝ) (n : ℕ) (C : SU2) :
    lagKernel r n C = iterateLaw r (Measure.dirac C) n := by
  induction n with
  | zero => simp [lagKernel, Kernel.id_apply, iterateLaw]
  | succ n ih =>
      change (loopKernel r ∘ₖ lagKernel r n) C =
        loopKernel r ∘ₘ iterateLaw r (Measure.dirac C) n
      rw [Kernel.comp_apply, ih]

def stationaryLagLaw (r : ℝ) (n : ℕ) : Measure (SU2 × SU2) :=
  equilibriumLaw r ⊗ₘ lagKernel r n

theorem lag_event_upper (r : ℝ) (n : ℕ) (A B : Set SU2)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    stationaryLagLaw r n (A ×ˢ B) ≤
      equilibriumLaw r A * equilibriumLaw r B +
        equilibriumLaw r A * (residualCoefficient r)^n := by
  letI : IsProbabilityMeasure (equilibriumLaw r) := equilibriumLaw_probability r
  letI : IsMarkovKernel (lagKernel r n) := lagKernel_markov r n
  rw [stationaryLagLaw, Measure.compProd_apply_prod hA hB]
  calc
    (∫⁻ C in A, lagKernel r n C B ∂equilibriumLaw r) ≤
      ∫⁻ C in A, (equilibriumLaw r B + (residualCoefficient r)^n) ∂equilibriumLaw r := by
        apply lintegral_mono
        intro C
        change lagKernel r n C B ≤ _
        rw [lagKernel_apply]
        exact event_upper r (Measure.dirac C) n B
    _ = _ := by rw [setLIntegral_const]; ring


theorem lag_event_lower (r : ℝ) (n : ℕ) (A B : Set SU2)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    equilibriumLaw r A * equilibriumLaw r B ≤
      stationaryLagLaw r n (A ×ˢ B) +
        equilibriumLaw r A * (residualCoefficient r)^n := by
  letI : IsProbabilityMeasure (equilibriumLaw r) := equilibriumLaw_probability r
  letI : IsMarkovKernel (lagKernel r n) := lagKernel_markov r n
  rw [stationaryLagLaw, Measure.compProd_apply_prod hA hB]
  have hpoint (C : SU2) : equilibriumLaw r B ≤
      lagKernel r n C B + (residualCoefficient r)^n := by
    rw [lagKernel_apply]
    exact event_lower r (Measure.dirac C) n B
  have hint := lintegral_mono (μ := (equilibriumLaw r).restrict A) hpoint
  rw [lintegral_add_left ((lagKernel r n).measurable_coe hB), lintegral_const,
    lintegral_const] at hint
  simpa only [Measure.restrict_apply_univ, mul_comm] using hint

theorem lagKernel_stationary (r : ℝ) (n : ℕ) :
    lagKernel r n ∘ₘ equilibriumLaw r = equilibriumLaw r := by
  induction n with
  | zero =>
      change (Kernel.id : Kernel SU2 SU2) ∘ₘ equilibriumLaw r = equilibriumLaw r
      change (equilibriumLaw r).bind Measure.dirac = equilibriumLaw r
      exact Measure.bind_dirac
  | succ n ih =>
      change (loopKernel r ∘ₖ lagKernel r n) ∘ₘ equilibriumLaw r = equilibriumLaw r
      rw [← Measure.comp_assoc, ih, equilibriumLaw_stationary]

theorem stationaryLagLaw_fst (r : ℝ) (n : ℕ) :
    (stationaryLagLaw r n).fst = equilibriumLaw r := by
  letI : IsMarkovKernel (lagKernel r n) := lagKernel_markov r n
  letI : IsProbabilityMeasure (equilibriumLaw r) := equilibriumLaw_probability r
  exact Measure.fst_compProd (equilibriumLaw r) (lagKernel r n)

theorem stationaryLagLaw_snd (r : ℝ) (n : ℕ) :
    (stationaryLagLaw r n).snd = equilibriumLaw r := by
  letI : IsMarkovKernel (lagKernel r n) := lagKernel_markov r n
  letI : IsProbabilityMeasure (equilibriumLaw r) := equilibriumLaw_probability r
  rw [stationaryLagLaw, Measure.snd_compProd]
  exact lagKernel_stationary r n

theorem lag_event_tendsto_product (r : ℝ) (A B : Set SU2)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ => stationaryLagLaw r n (A ×ˢ B)) atTop
      (𝓝 (equilibriumLaw r A * equilibriumLaw r B)) := by
  letI : IsProbabilityMeasure (equilibriumLaw r) := equilibriumLaw_probability r
  have hAfinite : equilibriumLaw r A ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ A))
  have hBfinite : equilibriumLaw r B ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ B))
  have hprodFinite : equilibriumLaw r A * equilibriumLaw r B ≠ ⊤ :=
    ENNReal.mul_ne_top hAfinite hBfinite
  have hpow : Tendsto (fun n : ℕ => (residualCoefficient r)^n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (c_lt_one r)
  have herr : Tendsto (fun n : ℕ => equilibriumLaw r A * (residualCoefficient r)^n)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hpow (Or.inr hAfinite)
  have hlow : Tendsto
      (fun n : ℕ => equilibriumLaw r A * equilibriumLaw r B -
        equilibriumLaw r A * (residualCoefficient r)^n) atTop
      (𝓝 (equilibriumLaw r A * equilibriumLaw r B)) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds herr (Or.inl hprodFinite)
  have hupp : Tendsto
      (fun n : ℕ => equilibriumLaw r A * equilibriumLaw r B +
        equilibriumLaw r A * (residualCoefficient r)^n) atTop
      (𝓝 (equilibriumLaw r A * equilibriumLaw r B)) := by
    simpa using (tendsto_const_nhds.add herr)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
  · intro n
    exact tsub_le_iff_right.mpr (lag_event_lower r n A B hA hB)
  · intro n
    exact lag_event_upper r n A B hA hB
end OperatorDerivativeRewrite.Foundation.SU2LagEventCorrelation
