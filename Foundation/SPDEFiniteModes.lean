import Foundation.SPDEModulatedSensitivity
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-! Orthogonal finite Brownian time modes for genuine spectral forcing. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.SPDEFiniteModes
open GaussianTimeHilbert GaussianHilbertProcess InfiniteGaussian
open SPDEModulatedResponse SPDEModulatedSensitivity
attribute [local instance] timeHilbert_secondCountable

abbrev ModeHilbert (n : ℕ) := PiLp 2 (fun _ : Fin n => TimeHilbert)

instance (n : ℕ) : SecondCountableTopology (ModeHilbert n) := by infer_instance

def modeVector {n : ℕ} (i : Fin n) (v : TimeHilbert) : ModeHilbert n :=
  PiLp.single 2 i v

theorem modeVector_inner {n : ℕ} (i j : Fin n) (v w : TimeHilbert) :
    inner ℝ (modeVector i v) (modeVector j w) =
      if i = j then inner ℝ v w else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [modeVector, PiLp.inner_apply, PiLp.single_apply, ite_true]
    have ht (x : Fin n) :
        inner ℝ (if x = i then v else 0) (if x = i then w else 0) =
          if x = i then inner ℝ v w else 0 := by
      by_cases hx : x = i <;> simp [hx]
    simp_rw [ht]
    simp
  · simp only [modeVector, PiLp.inner_apply, PiLp.single_apply]
    have ht (x : Fin n) :
        inner ℝ (if x = i then v else 0) (if x = j then w else 0) = 0 := by
      by_cases hx : x = i
      · simp [hx, hij]
      · simp [hx]
    simp_rw [ht]
    simp [hij]

def brownianMode {n : ℕ} (i : Fin n) (t : ℝ≥0) : SampleSpace → ℝ :=
  isonormal (ModeHilbert n) (modeVector i (timeVector t))

theorem brownianModes_jointGaussian {n : ℕ} :
    IsGaussianProcess
      (fun p : (_ : Fin n) × ℝ≥0 => brownianMode p.1 p.2) gaussianProduct := by
  exact isonormal_isGaussianProcess.comp_right
    (fun p : (_ : Fin n) × ℝ≥0 => modeVector p.1 (timeVector p.2))

theorem brownianMode_cross_moment {n : ℕ} (i j : Fin n) (s t : ℝ≥0) :
    (∫ ω, brownianMode i s ω * brownianMode j t ω ∂gaussianProduct) =
      if i = j then min (s : ℝ) (t : ℝ) else 0 := by
  rw [brownianMode, brownianMode, isonormal_product_integral,
    modeVector_inner, timeVector_inner]

theorem brownianModes_independent {n : ℕ} :
    iIndepFun (fun i ω t => brownianMode (n := n) i t ω) gaussianProduct := by
  apply IsGaussianProcess.iIndepFun_of_covariance_eq_zero
    (T := Fin n) (S := fun _ => ℝ≥0) (P := gaussianProduct)
    (X := fun i t => brownianMode i t) (brownianModes_jointGaussian (n := n))
  · intro i t
    exact (isonormal_measurable _).aemeasurable
  · intro i j hij s t
    change cov[isonormal (ModeHilbert n) (modeVector i (timeVector s)),
      isonormal (ModeHilbert n) (modeVector j (timeVector t)); gaussianProduct] = 0
    rw [isonormal_covariance, modeVector_inner]
    simp [hij]

def modeResponse {n : ℕ} (i : Fin n) (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ)
    (hupper : ∀ s, |g s| ≤ M) : GaussianL2 :=
  isonormalEmbedding (ModeHilbert n)
    (modeVector i (modulatedVector α hα t g hg M hupper))

theorem modeResponse_energy {n : ℕ} (i : Fin n) (α : ℝ)
    (hα : 1 / 2 < α) (t : ℝ≥0) (g : ℝ → ℝ)
    (hg : Measurable g) (M : ℝ) (hupper : ∀ s, |g s| ≤ M) :
    ‖modeResponse i α hα t g hg M hupper‖ ^ 2 =
      ∫ s, (modulatedResponse α t g s)^2 := by
  rw [modeResponse, LinearIsometry.norm_map, modeVector, PiLp.norm_single,
    modulatedVector_energy]

theorem modeResponse_cross_moment {n : ℕ} (i j : Fin n)
    (α : ℝ) (hα : 1 / 2 < α) (t : ℝ≥0)
    (g h : ℝ → ℝ) (hg : Measurable g) (hh : Measurable h)
    (Mg Mh : ℝ) (hgM : ∀ s, |g s| ≤ Mg) (hhM : ∀ s, |h s| ≤ Mh) :
    (∫ ω, isonormal (ModeHilbert n)
        (modeVector i (modulatedVector α hα t g hg Mg hgM)) ω *
      isonormal (ModeHilbert n)
        (modeVector j (modulatedVector α hα t h hh Mh hhM)) ω
      ∂gaussianProduct) =
      if i = j then
        ∫ s, modulatedResponse α t g s * modulatedResponse α t h s
      else 0 := by
  rw [isonormal_product_integral, modeVector_inner]
  split_ifs with hij
  · have hc := modulated_cross_moment α hα t g h hg hh Mg Mh hgM hhM
    simpa only [isonormal_product_integral] using hc
  · rfl

def finiteGaussianResponse {n : ℕ} (c : Fin n → ℝ)
    (v : Fin n → TimeHilbert) : GaussianL2 :=
  isonormalEmbedding (ModeHilbert n)
    (∑ i, c i • modeVector i (v i))

theorem finiteGaussianResponse_energy {n : ℕ} (c : Fin n → ℝ)
    (v : Fin n → TimeHilbert) :
    ‖finiteGaussianResponse c v‖ ^ 2 =
      ∑ i, (c i)^2 * ‖v i‖^2 := by
  classical
  rw [finiteGaussianResponse, LinearIsometry.norm_map,
    ← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoord : ((∑ i, c i • modeVector i (v i) : ModeHilbert n).ofLp j) =
      c j • v j := by
    simp [modeVector, Pi.single_apply]
  rw [hcoord, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs]

def finiteModulatedResponse {n : ℕ} (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : Fin n → ℝ → ℝ)
    (hg : ∀ i, Measurable (g i)) (M : Fin n → ℝ)
    (hM : ∀ i s, |g i s| ≤ M i) (c : Fin n → ℝ) : GaussianL2 :=
  finiteGaussianResponse c
    (fun i => modulatedVector α hα t (g i) (hg i) (M i) (hM i))

/-- Exact energy of every scalar observation of finitely many orthogonal
Brownian forcing modes. The coefficients may include square-root noise weights. -/
theorem finiteModulatedResponse_energy {n : ℕ} (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : Fin n → ℝ → ℝ)
    (hg : ∀ i, Measurable (g i)) (M : Fin n → ℝ)
    (hM : ∀ i s, |g i s| ≤ M i) (c : Fin n → ℝ) :
    ‖finiteModulatedResponse α hα t g hg M hM c‖^2 =
      ∑ i, (c i)^2 * ∫ s, (modulatedResponse α t (g i) s)^2 := by
  rw [finiteModulatedResponse, finiteGaussianResponse_energy]
  congr 1
  funext i
  rw [modulatedVector_energy]

end OperatorDerivativeRewrite.Foundation.SPDEFiniteModes
