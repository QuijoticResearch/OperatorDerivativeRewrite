import Foundation.GaussianTiltHalfDensity

/-! Half-density multiplication as an actual equivalence of the two L2 quotient spaces. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianHalfDensityUnitary
open InfiniteGaussian GaussianLinearTiltLaw GaussianTiltHalfDensity
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Qlinear := Qlinear_probability

abbrev QSpace := Lp ℝ 2 Qlinear

theorem forward_memLp (u : QSpace) : MemLp (transport u) 2 gaussianProduct :=
  (transport_memLp_iff (Lp.stronglyMeasurable u).measurable).mpr (Lp.memLp u)

def forward (u : QSpace) : InfiniteGaussian.GaussianL2 := (forward_memLp u).toLp (transport u)

theorem forward_coeFn (u : QSpace) : forward u =ᵐ[gaussianProduct] transport u :=
  MemLp.coeFn_toLp _

theorem backward_memLp (v : InfiniteGaussian.GaussianL2) : MemLp (inverse v) 2 Qlinear :=
  (inverse_memLp_iff (Lp.stronglyMeasurable v).measurable).mpr (Lp.memLp v)

def backward (v : InfiniteGaussian.GaussianL2) : QSpace := (backward_memLp v).toLp (inverse v)

theorem backward_coeFn (v : InfiniteGaussian.GaussianL2) : backward v =ᵐ[Qlinear] inverse v :=
  MemLp.coeFn_toLp _

theorem forward_add (u v : QSpace) : forward (u+v) = forward u + forward v := by
  apply Lp.ext
  filter_upwards [forward_coeFn (u+v), forward_coeFn u, forward_coeFn v,
    P_ac_Qlinear.ae_le (Lp.coeFn_add u v), Lp.coeFn_add (forward u) (forward v)] with ω h h₁ h₂ ha hb
  rw [h, hb]
  change GaussianTiltL2Domain.rootDensity ω * (u+v) ω = forward u ω + forward v ω
  rw [ha, h₁, h₂]
  simp only [transport, Pi.add_apply]
  ring

theorem forward_smul (r : ℝ) (u : QSpace) : forward (r • u) = r • forward u := by
  apply Lp.ext
  filter_upwards [forward_coeFn (r • u), forward_coeFn u,
    P_ac_Qlinear.ae_le (Lp.coeFn_smul r u), Lp.coeFn_smul r (forward u)] with ω h h₁ ha hb
  rw [h, hb]
  change GaussianTiltL2Domain.rootDensity ω * (r • u) ω = r * forward u ω
  rw [ha, h₁]
  simp only [transport, Pi.smul_apply, smul_eq_mul]
  ring

def forwardLinear : QSpace →ₗ[ℝ] InfiniteGaussian.GaussianL2 where
  toFun := forward
  map_add' := forward_add
  map_smul' := forward_smul

theorem backward_forward (u : QSpace) : backward (forward u) = u := by
  apply Lp.ext
  filter_upwards [backward_coeFn (forward u), Qlinear_ac_P.ae_le (forward_coeFn u)] with ω hb hf
  rw [hb]
  change forward u ω / GaussianTiltL2Domain.rootDensity ω = u ω
  rw [hf]
  change GaussianTiltL2Domain.rootDensity ω * u ω / GaussianTiltL2Domain.rootDensity ω = u ω
  field_simp [(rootDensity_positive ω).ne']

theorem forward_backward (v : InfiniteGaussian.GaussianL2) : forward (backward v) = v := by
  apply Lp.ext
  filter_upwards [forward_coeFn (backward v), P_ac_Qlinear.ae_le (backward_coeFn v)] with ω hf hb
  rw [hf]
  change GaussianTiltL2Domain.rootDensity ω * backward v ω = v ω
  rw [hb]
  change GaussianTiltL2Domain.rootDensity ω * (v ω / GaussianTiltL2Domain.rootDensity ω) = v ω
  field_simp [(rootDensity_positive ω).ne']

theorem square_lintegral_norm {μ : Measure SampleSpace} (u : Lp ℝ 2 μ) :
    (∫⁻ ω, ENNReal.ofReal (u ω ^ 2) ∂μ) = ENNReal.ofReal (‖u‖^2) := by
  have hn : ‖u‖^2 = ∫ ω, u ω ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [pow_two]
  rw [hn]
  exact (ofReal_integral_eq_lintegral_ofReal (Lp.memLp u).integrable_sq
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (u ω)))).symm

theorem forward_norm (u : QSpace) : ‖forward u‖ = ‖u‖ := by
  have hs : ENNReal.ofReal (‖forward u‖^2) = ENNReal.ofReal (‖u‖^2) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (forward u ω ^ 2) ∂gaussianProduct :=
        (square_lintegral_norm (forward u)).symm
      _ = ∫⁻ ω, ENNReal.ofReal (transport u ω ^ 2) ∂gaussianProduct := by
        apply lintegral_congr_ae
        filter_upwards [forward_coeFn u] with ω hω
        rw [hω]
      _ = ∫⁻ ω, ENNReal.ofReal (u ω ^ 2) ∂Qlinear :=
        square_lintegral (Lp.stronglyMeasurable u).measurable
      _ = _ := square_lintegral_norm u
  have he : ‖forward u‖^2 = ‖u‖^2 := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using congrArg ENNReal.toReal hs
  nlinarith [norm_nonneg (forward u), norm_nonneg u]

def unitary : QSpace ≃ₗᵢ[ℝ] InfiniteGaussian.GaussianL2 where
  toLinearEquiv := LinearEquiv.ofBijective forwardLinear
    ⟨(show Function.LeftInverse backward forward from backward_forward).injective,
      (show Function.RightInverse backward forward from forward_backward).surjective⟩
  norm_map' := forward_norm

theorem unitary_apply (u : QSpace) : unitary u = forward u := rfl

theorem unitary_coeFn (u : QSpace) : unitary u =ᵐ[gaussianProduct] transport u :=
  forward_coeFn u

theorem unitary_symm_apply (v : InfiniteGaussian.GaussianL2) : unitary.symm v = backward v := by
  apply unitary.injective
  rw [unitary.apply_symm_apply, unitary_apply, forward_backward]

theorem unitary_symm_coeFn (v : InfiniteGaussian.GaussianL2) :
    unitary.symm v =ᵐ[Qlinear] inverse v := by
  rw [unitary_symm_apply]
  exact backward_coeFn v

end OperatorDerivativeRewrite.Foundation.GaussianHalfDensityUnitary
