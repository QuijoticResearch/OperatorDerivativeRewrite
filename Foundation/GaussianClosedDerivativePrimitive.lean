import Foundation.GaussianHermiteDomains
import Foundation.GaussianLocalSobolev
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Necessity of an actual local primitive for the ORIGINAL closed scalar
Gaussian derivative. This is not an assumption of pointwise differentiability. -/
noncomputable section
open MeasureTheory Filter Set Polynomial
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianClosedDerivativePrimitive
open GaussianCore

def localize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : ℝ) :
    Lp E 2 γ →L[ℝ] Lp E 2 (volume.restrict (Icc a b)) :=
  Lp.LpToLpOfMeasureLeSMul
    (GaussianLocalSobolev.exists_local_measure_comparison a b).choose_spec.2.1
    (GaussianLocalSobolev.exists_local_measure_comparison a b).choose_spec.2.2

theorem localize_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (f : Lp E 2 γ) : localize a b f =ᵐ[volume.restrict (Icc a b)] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _

def localIntegral (a b : ℝ) : GaussianL2 →L[ℝ] ℝ :=
  (innerSL ℝ (Lp.const 2 (volume.restrict (Icc a b)) (1 : ℝ))).comp (localize a b)

theorem localIntegral_eq (a b : ℝ) (f : GaussianL2) :
    localIntegral a b f = ∫ x in Icc a b, f x := by
  change inner ℝ (Lp.const 2 (volume.restrict (Icc a b)) (1 : ℝ)) (localize a b f) = _
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (p := 2) (μ := volume.restrict (Icc a b)) (c := (1 : ℝ)),
    localize_ae a b f] with x hc hf
  rw [hc, hf]
  simp only [Function.const_apply, Real.inner_apply, one_mul]

theorem localIntegral_tendsto {u : ℕ → GaussianL2} {g : GaussianL2}
    (hu : Tendsto u atTop (𝓝 g)) (a b : ℝ) :
    Tendsto (fun n => ∫ x in Icc a b, u n x) atTop (𝓝 (∫ x in Icc a b, g x)) := by
  simpa only [Function.comp_def, localIntegral_eq] using
    (localIntegral a b).continuous.tendsto g |>.comp hu

theorem polynomial_local_primitive (p : ℝ[X]) {a x : ℝ} (hax : a ≤ x) :
    (∫ y in Icc a x, polynomialL2 p.derivative y) = p.eval x - p.eval a := by
  have hv : (volume : Measure ℝ) ≪ γ :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)
  rw [integral_congr_ae (ae_restrict_of_ae (hv.ae_eq (polynomialL2_coeFn p.derivative))),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hax]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => polynomial_hasDerivAt p y) (p.derivative.continuous.intervalIntegrable a x)

/-- Hermite graph approximation, a common AE value subsequence and continuous
local integral functionals recover the primitive of the genuine closed graph. -/
theorem closed_graph_primitive {f g : GaussianL2} (hfg : (f, g) ∈ closedDerivative.graph)
    {a b : ℝ} (hab : a < b) :
    ∃ c : ℝ, f =ᵐ[volume.restrict (Icc a b)] fun x => c + ∫ y in Icc a x, g y := by
  have hh := divergence_adjoint_hermite_approximation f g
    (by rwa [← closedDerivative_eq_divergence_adjoint])
  have hp : ∀ n, ∃ p : ℝ[X],
      (polynomialL2 p, polynomialL2 p.derivative) =
        (hermiteTruncation f (n + 1), hermiteTruncation g n) := by
    intro n
    have hn := hh.1 n
    rw [polynomialDerivative_graph] at hn
    exact hn
  choose p hp using hp
  have hu : Tendsto (fun n => polynomialL2 (p n)) atTop (𝓝 f) := by
    have he (n : ℕ) : polynomialL2 (p n) = hermiteTruncation f (n + 1) :=
      congrArg Prod.fst (hp n)
    simpa only [he] using hh.2.fst_nhds
  have hg : Tendsto (fun n => polynomialL2 (p n).derivative) atTop (𝓝 g) := by
    have he (n : ℕ) : polynomialL2 (p n).derivative = hermiteTruncation g n :=
      congrArg Prod.snd (hp n)
    simpa only [he] using hh.2.snd_nhds
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  have hv : (volume : Measure ℝ) ≪ γ :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)
  have hpoly : ∀ᵐ x ∂γ, ∀ n, polynomialL2 (p (ns n)) x = (p (ns n)).eval x :=
    ae_all_iff.mpr (fun n => polynomialL2_coeFn _)
  have hl : ∀ᵐ x ∂volume.restrict (Icc a b),
      Tendsto (fun n => (p (ns n)).eval x) atTop (𝓝 (f x)) := by
    filter_upwards [ae_restrict_of_ae (hv.ae_le hae),
      ae_restrict_of_ae (hv.ae_le hpoly)] with x hx hp
    simpa only [hp] using hx
  obtain ⟨z, hz, hzl⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (show (volume : Measure ℝ) (Icc a b) ≠ 0 by
      rw [Real.volume_Icc]
      exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne') hl
  refine ⟨f z - ∫ y in Icc a z, g y, ?_⟩
  filter_upwards [hl, ae_restrict_mem measurableSet_Icc] with x hx hxi
  have hleft := hx.sub hzl
  have hright := (localIntegral_tendsto (hg.comp hns.tendsto_atTop) a x).sub
    (localIntegral_tendsto (hg.comp hns.tendsto_atTop) a z)
  have he (n : ℕ) : (p (ns n)).eval x - (p (ns n)).eval z =
      (∫ y in Icc a x, polynomialL2 (p (ns n)).derivative y) -
      ∫ y in Icc a z, polynomialL2 (p (ns n)).derivative y := by
    rw [polynomial_local_primitive _ hxi.1, polynomial_local_primitive _ hz.1]
    ring
  have hv := tendsto_nhds_unique hleft (by simpa only [Function.comp_def, ← he] using hright)
  linarith

/-- A continuous representative of the original closed derivative satisfies
the local FTC everywhere, including both endpoints. -/
theorem continuous_representative_FTC {f g : GaussianL2}
    (hfg : (f, g) ∈ closedDerivative.graph) {a b : ℝ} (hab : a < b)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Icc a b))
    (hrep : F =ᵐ[volume.restrict (Icc a b)] f) :
    ∀ x ∈ Icc a b, F x - F a = ∫ y in Icc a x, g y := by
  obtain ⟨c, hc⟩ := closed_graph_primitive hfg hab
  have hg := GaussianLocalSobolev.memLp_two_volume_restrict_Icc_of_memLp_gaussian a b (Lp.memLp g)
  have he := Measure.eqOn_of_ae_eq (hrep.trans hc) hF
    (continuousOn_const.add (intervalIntegral.continuousOn_primitive_Icc
      (hg.integrable (by norm_num))))
    (show Icc a b ⊆ closure (interior (Icc a b)) by rw [closure_interior_Icc hab.ne])
  have ha : F a = c := by simpa using he ⟨le_rfl, hab.le⟩
  intro x hx
  rw [he hx, ha]
  ring

end OperatorDerivativeRewrite.Foundation.GaussianClosedDerivativePrimitive
