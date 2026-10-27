import Foundation.CauchyPoissonForwardDual
/-! Point-mass laws obstruct strong continuity of the actual forward dual at
time zero for every admissible drift. At zero drift their transposed generator
pairing has no bounded value. This does not obstruct weak law evolution or
positive-time density domains. -/
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonDualObstruction
open CauchyPoissonForwardDual CauchyPoissonGeneratorDomain CauchyPoissonMarkovKernel
open CauchyPoissonCoreGenerator CauchyPoissonDomainDensity CauchyPoissonFlow

theorem dirac_apply (x : Circle) (f : C(Circle,ℂ)) :
    lawFunctional (Measure.dirac x) f = f x := by
  change (∫ z, f z ∂Measure.dirac x) = f x
  exact integral_dirac f x

theorem dirac_dual_power_norm (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (x : Circle) (n : ℕ) :
    ‖dualOrbit q hq (lawFunctional (Measure.dirac x)) t (coordinate^n)‖ =
      ‖evolution q t x‖^n := by
  rw [dualOrbit_apply,dirac_apply,orbit_power]
  change ‖(evolution q (max t 0) x)^n‖ = _
  rw [max_eq_left ht,norm_pow]

theorem dirac_dual_norm_gap (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (x : Circle) :
    1 ≤ ‖dualOrbit q hq (lawFunctional (Measure.dirac x)) t - lawFunctional (Measure.dirac x)‖ := by
  have hr := evolution_strict_disk q t hq ht x (by simp)
  have hp : Tendsto (fun n : ℕ => ‖evolution q t x‖^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hr
  have hh : ∀ n : ℕ, 1-‖evolution q t x‖^n ≤
      ‖dualOrbit q hq (lawFunctional (Measure.dirac x)) t - lawFunctional (Measure.dirac x)‖ := by
    intro n
    have hb := (dualOrbit q hq (lawFunctional (Measure.dirac x)) t -
      lawFunctional (Measure.dirac x)).le_opNorm (coordinate^n)
    rw [coordinate_power_norm,mul_one] at hb
    have hl := norm_sub_norm_le (lawFunctional (Measure.dirac x) (coordinate^n))
      (dualOrbit q hq (lawFunctional (Measure.dirac x)) t (coordinate^n))
    rw [dirac_dual_power_norm q t hq ht.le x n,dirac_apply] at hl
    have he : ‖(coordinate^n) x‖ = 1 := by change ‖(x:ℂ)^n‖=1; simp
    rw [he,norm_sub_rev] at hl
    simp only [sub_apply,dirac_apply] at hb
    exact hl.trans hb
  have hl : Tendsto (fun n : ℕ => 1-‖evolution q t x‖^n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hp
  exact le_of_tendsto hl (Eventually.of_forall hh)

theorem dirac_dual_not_strong_right (q : ℝ) (hq : |q| < 1) (x : Circle) :
    ¬ Tendsto (fun t => dualOrbit q hq (lawFunctional (Measure.dirac x)) t)
      (𝓝[Ioi 0] 0) (𝓝 (lawFunctional (Measure.dirac x))) := by
  intro h
  have hn : Tendsto (fun t => ‖dualOrbit q hq (lawFunctional (Measure.dirac x)) t -
      lawFunctional (Measure.dirac x)‖) (𝓝[Ioi 0] 0) (𝓝 0) := by
    simpa using (h.sub (tendsto_const_nhds (x := lawFunctional (Measure.dirac x)))).norm
  have he : ∀ᶠ t in 𝓝[Ioi (0:ℝ)] 0,
      1 ≤ ‖dualOrbit q hq (lawFunctional (Measure.dirac x)) t - lawFunctional (Measure.dirac x)‖ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact dirac_dual_norm_gap q t hq ht x
  have hh : (1:ℝ) ≤ 0 := ge_of_tendsto hn he
  norm_num at hh


-- The transpose on the entire generator graph has no bounded value at a Dirac law.
theorem zero_dirac_no_adjoint_value (x : Circle) :
    ¬ ∃ ψ : C(Circle,ℂ) →L[ℂ] ℂ, ∀ f g : C(Circle,ℂ),
      (f,g) ∈ (generator 0 (by norm_num)).graph →
      ψ f = lawFunctional (Measure.dirac x) g := by
  rintro ⟨ψ,hψ⟩
  obtain ⟨n,hn⟩ := exists_nat_gt ‖ψ‖
  have hg : (coordinate^n,powerVelocity 0 n) ∈ (generator 0 (by norm_num)).graph := by
    rw [generator_graph_iff]
    have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp
      (power_hasDerivWithinAt 0 (by norm_num) n)
    change Tendsto (fun t : ℝ => (t-0)⁻¹ • (orbit 0 (by norm_num) (coordinate^n) t-
      orbit 0 (by norm_num) (coordinate^n) 0)) _ _ at h
    simpa only [Tangent,sub_zero,orbit_zero] using h
  have hb := ψ.le_opNorm (coordinate^n)
  rw [hψ _ _ hg,coordinate_power_norm,mul_one,dirac_apply,zero_power_velocity] at hb
  have he : ‖((-(n:ℂ)) • coordinate^n) x‖ = (n:ℝ) := by
    change ‖(-(n:ℂ))*(x:ℂ)^n‖ = (n:ℝ)
    simp
  rw [he] at hb
  exact (not_le_of_gt hn) hb

end OperatorDerivativeRewrite.Foundation.CauchyPoissonDualObstruction
