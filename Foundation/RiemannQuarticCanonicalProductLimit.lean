import Foundation.RiemannQuarticCanonicalReconstruction
import Mathlib.Analysis.Normed.Field.Lemmas

/-! Actual finite canonical products approximate the quartic transform
locally uniformly. These are analytic rational products on expanding
disks; conversion to real split polynomials remains a separate obligation. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalProductLimit
open RiemannQuarticFlow RiemannQuarticCanonicalReconstruction

theorem exists_actual_product_approximation (t : ℝ) :
    ∃ r : ℝ → ℝ, ∃ h : ℝ → ℂ → ℂ,
      (∀ R : ℝ, 1 ≤ R → 2*R < r R ∧ r R < 2*R+1 ∧
        ECanonicalDecomp (flow t) (h R) (r R) ∧
        divisor (flow t) (sphere 0 (r R)) = 0 ∧
        inverseZeroProduct t (r R) 0 ≠ 0 ∧
        ∀ z ∈ closedBall (0 : ℂ) (r R),
          flow t z = inverseZeroProduct t (r R) z * h R z) ∧
      TendstoLocallyUniformly
        (fun R z => inverseZeroProduct t (r R) z / inverseZeroProduct t (r R) 0)
        (fun z => flow t z / flow t 0) atTop ∧
      TendstoLocallyUniformly
        (fun R z => flow t 0 * (inverseZeroProduct t (r R) z / inverseZeroProduct t (r R) 0))
        (flow t) atTop := by
  obtain ⟨A,hA,r,h,g,hs,hlog,hexp,hquot⟩ :=
    RiemannQuarticCanonicalLimit.exists_actual_locally_uniform_remainders t
  have hdata (R : ℝ) (hR : 1 ≤ R) : 2*R < r R ∧ r R < 2*R+1 ∧
      ECanonicalDecomp (flow t) (h R) (r R) ∧
      divisor (flow t) (sphere 0 (r R)) = 0 ∧
      inverseZeroProduct t (r R) 0 ≠ 0 ∧
      ∀ z ∈ closedBall (0 : ℂ) (r R), flow t z = inverseZeroProduct t (r R) z * h R z := by
    obtain ⟨hrl,hru,hbd,D,hg,h0,hd0,hd,he,hre⟩ := hs R hR
    have hrp : 0 < r R := by linarith
    exact ⟨hrl,hru,D,hbd,inverseZeroProduct_origin_ne_zero t (r R) hrp (h R) D hbd,
      actual_reconstruction t (r R) hrp (h R) D hbd⟩
  let F : ℂ → ℂ := fun z => flow t z / flow t 0
  have hFc : Continuous F := (flow_differentiable t).continuous.div_const _
  have hconst : TendstoLocallyUniformly (fun _ : ℝ => F) F atTop := by
    apply TendstoUniformly.tendstoLocallyUniformly
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    exact Eventually.of_forall fun R z => by simpa using hε
  have hdiv : TendstoLocallyUniformly (fun R z => F z / (h R z/h R 0)) F atTop := by
    have hh := hconst.div₀ hquot hFc continuous_const (by intro z; norm_num)
    have he : F / (fun _ : ℂ => (1 : ℂ)) = F := by funext z; simp
    rw [he] at hh
    exact hh
  have hprod : TendstoLocallyUniformly
      (fun R z => inverseZeroProduct t (r R) z / inverseZeroProduct t (r R) 0) F atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨ρ,hρ,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
    apply (tendstoLocallyUniformly_iff_forall_isCompact.mp hdiv K hK).congr
    filter_upwards [eventually_ge_atTop (max 1 (ρ+1))] with R hR
    have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
    obtain ⟨hrl,hru,D,hbd,hB0,hrec⟩ := hdata R hR1
    have hrp : 0 < r R := by linarith
    intro z hz
    have hzr : z ∈ closedBall (0 : ℂ) (r R) := mem_closedBall_zero_iff.mpr (by
      have hn := mem_closedBall_zero_iff.mp (hsub hz)
      linarith [(le_max_right 1 (ρ+1)).trans hR])
    have hn : h R z/h R 0 ≠ 0 := div_ne_zero (D.ne_zero z hzr)
      (D.ne_zero 0 (mem_closedBall_self hrp.le))
    have he := normalized_reconstruction t (r R) hrp (h R) D hbd z hzr
    exact ((eq_div_iff hn).mpr he.symm).symm
  have hscale : TendstoLocallyUniformly
      (fun R z => flow t 0 * (inverseZeroProduct t (r R) z / inverseZeroProduct t (r R) 0))
      (flow t) atTop := by
    have hc : TendstoLocallyUniformly (fun _ : ℝ => fun _ : ℂ => flow t 0)
        (fun _ => flow t 0) atTop := by
      apply TendstoUniformly.tendstoLocallyUniformly
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      exact Eventually.of_forall fun R z => by simpa using hε
    have hh := hc.mul₀ hprod continuous_const hFc
    have hn : flow t 0 ≠ 0 := by
      simpa using RiemannQuarticReality.flow_ne_zero_on_imaginary_axis t 0
    have he : (fun _ : ℂ => flow t 0) * F = flow t := by
      funext z
      dsimp [F]
      field_simp
    rw [he] at hh
    exact hh
  exact ⟨r,h,hdata,hprod,hscale⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalProductLimit
