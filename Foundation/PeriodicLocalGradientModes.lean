import Foundation.PeriodicSingleBlockDecomposition

/-! The sharp local coercivity bound is saturated exactly by fields with
vanishing internal curl. Restricted vertex gradients provide such fields,
although their zero extension generally has exterior curvature. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalGradientModes
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity
  PeriodicSingleBlockDecomposition
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem core_links_local : ∀ p : Core,
    localEdge (p.val.val.1,p.val.val.2.1) ∧
    localEdge (shift p.val.val.1 p.val.val.2.1,p.val.val.2.2) ∧
    localEdge (shift p.val.val.1 p.val.val.2.2,p.val.val.2.1) ∧
    localEdge (p.val.val.1,p.val.val.2.2) := by decide

def localGradient : (Vertex → ℝ) →ₗ[ℝ] (Local → ℝ) where
  toFun φ e := gradientMap φ e.val
  map_add' φ ψ := by ext e; simp
  map_smul' r φ := by ext e; simp

theorem localExtend_gradient (φ : Vertex → ℝ) (e : Edge) (he : localEdge e) :
    localExtend (localGradient φ) e=gradientMap φ e := by
  simp [localExtend,localGradient,he]

theorem coreIncidence_gradient (φ : Vertex → ℝ) :
    coreIncidence (localGradient φ)=0 := by
  ext p
  obtain ⟨h₁,h₂,h₃,h₄⟩ := core_links_local p
  change curl (localExtend (localGradient φ)) p.val.val.1
    p.val.val.2.1 p.val.val.2.2=0
  unfold curl
  rw [localExtend_gradient φ _ h₁,localExtend_gradient φ _ h₂,
    localExtend_gradient φ _ h₃,localExtend_gradient φ _ h₄]
  exact congrFun (incidence_gradient_zero φ) p.val

theorem coreEnergy_eq_norm (f : Local → ℝ) :
    coreEnergy f=∑ p : Core, (coreIncidence f p)^2 := by
  exact Finset.sum_subtype coreFaces (fun p => by simp [coreFaces])
    (fun p => (localIncidence f p)^2)

theorem coreEnergy_zero_iff (f : Local → ℝ) :
    coreEnergy f=0 ↔ coreIncidence f=0 := by
  rw [coreEnergy_eq_norm,Finset.sum_eq_zero_iff_of_nonneg (fun p _ => sq_nonneg _)]
  simp only [Finset.mem_univ,true_implies,pow_eq_zero_iff (by decide : 2 ≠ 0)]
  exact ⟨fun h => funext h,fun h p => congrFun h p⟩

theorem sharp_energy_iff (f : Local → ℝ) :
    energy f=3*squaredSize f ↔ coreIncidence f=0 := by
  rw [exact_energy_decomposition]
  constructor
  · intro h
    exact (coreEnergy_zero_iff f).mp (by linarith)
  · intro h
    rw [(coreEnergy_zero_iff f).mpr h,add_zero]

theorem coreGram_zero_iff (f : Local → ℝ) :
    coreGram.mulVec f=0 ↔ coreIncidence f=0 := by
  constructor
  · intro h
    apply (coreEnergy_zero_iff f).mp
    rw [← coreGram_energy,h,dotProduct_zero]
  · intro h
    rw [coreGram,← Matrix.mulVec_mulVec,coreMatrix_mulVec,h,Matrix.mulVec_zero]

theorem eigenvalue_three_iff (f : Local → ℝ) :
    localHessian.mulVec f=(3 : ℝ) • f ↔ coreIncidence f=0 := by
  rw [localHessian_decomposition,Matrix.add_mulVec,Matrix.ofNat_mulVec]
  exact (add_eq_left (a := (3 : ℝ) • f)).trans (coreGram_zero_iff f)

theorem gradient_eigenvalue_three (φ : Vertex → ℝ) :
    localHessian.mulVec (localGradient φ)=(3 : ℝ) • localGradient φ :=
  (eigenvalue_three_iff _).mpr (coreIncidence_gradient φ)

theorem gradient_energy (φ : Vertex → ℝ) :
    energy (localGradient φ)=3*squaredSize (localGradient φ) :=
  (sharp_energy_iff _).mpr (coreIncidence_gradient φ)

theorem localIncidence_injective : Function.Injective localIncidence :=
  PeriodicSingleBlockCoercivity.localIncidence_injective

theorem gradient_full_curl_zero_iff (φ : Vertex → ℝ) :
    localIncidence (localGradient φ)=0 ↔ localGradient φ=0 := by
  constructor
  · intro h
    apply localIncidence_injective
    simpa using h
  · intro h
    rw [h,map_zero]

end OperatorDerivativeRewrite.Foundation.PeriodicLocalGradientModes
