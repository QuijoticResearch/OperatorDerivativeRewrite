import Foundation.PeriodicLocalHodgeProjection

/-! Actual local quotient minima: orthogonal projection and an attained completed square. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalQuotientEnergy
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity PeriodicLocalGradientModes
  PeriodicLocalSpectralSet PeriodicLocalTransverseGap PeriodicLocalTransverseSharp
  PeriodicLocalTransverseSpace PeriodicLocalHodgeProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem dot_self_size (f : Field) : dotProduct f f = squaredSize f := by
  simp [dotProduct, PeriodicSingleBlockCoercivity.squaredSize, pow_two]

theorem squaredSize_nonneg (f : Field) : 0 ≤ squaredSize f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem squaredSize_add (f g : Field) : squaredSize (f+g) =
    squaredSize f+squaredSize g+2*dotProduct f g := by
  rw [← dot_self_size (f+g), add_dotProduct, dotProduct_add, dotProduct_add,
    dot_self_size, dot_self_size, dotProduct_comm g f]
  ring

theorem energy_dot (f : Field) : energy f = dotProduct f (H f) :=
  (hessian_energy f).symm

theorem energy_add (f g : Field) : energy (f+g) = energy f+energy g+2*dotProduct f (H g) := by
  have hc : dotProduct g (H f) = dotProduct f (H g) := by
    rw [dotProduct_comm g (H f)]
    exact (H_dot_symmetric f g).symm
  simp only [energy_dot, map_add, add_dotProduct, dotProduct_add, hc]
  ring

theorem transverse_gradient_orthogonal (f g : Field) (hf : transverse f)
    (hg : g ∈ LinearMap.range localGradient) : dotProduct f g=0 := by
  obtain ⟨φ, hφ⟩ := hg
  have h := hf φ
  rw [hφ] at h
  exact h

theorem gradient_H (g : Field) (hg : g ∈ LinearMap.range localGradient) : H g=(3 : ℝ) • g := by
  obtain ⟨φ, rfl⟩ := hg
  exact gradient_eigenvalue_three φ

theorem orthogonal_energy_split (f g : Field) (hf : transverse f)
    (hg : g ∈ LinearMap.range localGradient) : energy (f+g)=energy f+3*squaredSize g := by
  have he := eigenvector_energy g 3 (gradient_H g hg)
  rw [energy_add, gradient_H g hg, dotProduct_smul,
    transverse_gradient_orthogonal f g hf hg, smul_zero, he]
  ring

theorem orthogonal_size_split (f g : Field) (hf : transverse f)
    (hg : g ∈ LinearMap.range localGradient) : squaredSize (f+g)=squaredSize f+squaredSize g := by
  rw [squaredSize_add, transverse_gradient_orthogonal f g hf hg]
  ring

theorem shifted_decomposition (f : Field) (g : Field) :
    f+g=transverseProjection f+(gradientProjection f+g) := by
  calc
    f+g = (gradientProjection f+transverseProjection f)+g :=
      congrArg (fun v : Field => v+g) (decomposition f).symm
    _ = _ := by abel

theorem completed_square (f : Field) (φ : Vertex → ℝ) :
    energy (f+localGradient φ) = energy (transverseProjection f) +
      3*squaredSize (gradientProjection f+localGradient φ) := by
  rw [shifted_decomposition f (localGradient φ)]
  exact orthogonal_energy_split _ _ (transverseProjection_mem f)
    ((LinearMap.range localGradient).add_mem (gradientProjection_mem f) ⟨φ, rfl⟩)

theorem completed_size (f : Field) (φ : Vertex → ℝ) :
    squaredSize (f+localGradient φ) = squaredSize (transverseProjection f) +
      squaredSize (gradientProjection f+localGradient φ) := by
  rw [shifted_decomposition f (localGradient φ)]
  exact orthogonal_size_split _ _ (transverseProjection_mem f)
    ((LinearMap.range localGradient).add_mem (gradientProjection_mem f) ⟨φ, rfl⟩)

theorem energy_minimum_lower (f : Field) (φ : Vertex → ℝ) :
    energy (transverseProjection f) ≤ energy (f+localGradient φ) := by
  rw [completed_square]
  nlinarith [squaredSize_nonneg (gradientProjection f+localGradient φ)]

theorem size_minimum_lower (f : Field) (φ : Vertex → ℝ) :
    squaredSize (transverseProjection f) ≤ squaredSize (f+localGradient φ) := by
  rw [completed_size]
  exact le_add_of_nonneg_right (squaredSize_nonneg _)

theorem minimum_attained (f : Field) : ∃ φ : Vertex → ℝ,
    f+localGradient φ=transverseProjection f ∧
    energy (f+localGradient φ)=energy (transverseProjection f) ∧
    squaredSize (f+localGradient φ)=squaredSize (transverseProjection f) := by
  obtain ⟨ψ, hψ⟩ := gradientProjection_mem f
  refine ⟨-ψ, ?_⟩
  have he : f+localGradient (-ψ)=transverseProjection f := by
    rw [map_neg, hψ]
    rw [shifted_decomposition f (-gradientProjection f), add_neg_cancel, add_zero]
  exact ⟨he, congrArg energy he, congrArg PeriodicSingleBlockCoercivity.squaredSize he⟩

theorem equality_iff_cancel_gradient (f : Field) (φ : Vertex → ℝ) :
    energy (f+localGradient φ)=energy (transverseProjection f) ↔
      gradientProjection f+localGradient φ=0 := by
  rw [completed_square]
  constructor
  · intro h
    have hn : squaredSize (gradientProjection f+localGradient φ)=0 := by linarith
    exact (squaredSize_zero_iff _).mp hn
  · intro h
    rw [h]
    simp [PeriodicSingleBlockCoercivity.squaredSize]

theorem minimizing_field_unique (f : Field) (φ : Vertex → ℝ) :
    energy (f+localGradient φ)=energy (transverseProjection f) ↔
      f+localGradient φ=transverseProjection f := by
  rw [equality_iff_cancel_gradient]
  rw [shifted_decomposition f (localGradient φ)]
  simp only [add_eq_left]

theorem transverseProjection_coset_iff (f g : Field) : transverseProjection f=transverseProjection g ↔
    f-g ∈ LinearMap.range localGradient := by
  rw [← transverseProjection_kernel, LinearMap.mem_ker, map_sub, sub_eq_zero]

theorem quotient_energy_bounds (f : Field) :
    7*squaredSize (transverseProjection f) ≤ energy (transverseProjection f) ∧
    energy (transverseProjection f) ≤ 11*squaredSize (transverseProjection f) :=
  ⟨transverse_coercive (transverseProjection_mem f),
    transverse_upper_bound (transverseProjection_mem f)⟩

end OperatorDerivativeRewrite.Foundation.PeriodicLocalQuotientEnergy
