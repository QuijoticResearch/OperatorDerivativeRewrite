import Foundation.SchwartzFractionalL2Fields

/-! A single narrow angular cap and real-field Fourier symmetry. -/
noncomputable section
open MeasureTheory Set
open scoped Topology FourierTransform SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.SingleConeReality
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def direction (ξ : V) : V := ‖ξ‖⁻¹ • ξ
def cone (n : V) (δ : ℝ) : Set V := {ξ | ξ≠0 ∧ ‖direction ξ-n‖<δ}

theorem direction_neg (ξ : V) : direction (-ξ) = -direction ξ := by
  simp [direction]

theorem direction_norm {ξ : V} (hξ : ξ≠0) : ‖direction ξ‖=1 := by
  rw [direction, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)

theorem no_unit_antipodes (u n : V) (hu : ‖u‖=1) (δ : ℝ) (hδ : δ≤1)
    (hp : ‖u-n‖<δ) (hm : ‖-u-n‖<δ) : False := by
  have hh := norm_sub_le (u-n) (-u-n)
  have he : (u-n)-(-u-n)=(2:ℝ) • u := by module
  rw [he, norm_smul, hu] at hh
  norm_num at hh
  linarith

theorem cone_no_antipodes (n : V) (δ : ℝ) (hδ : δ≤1) {ξ : V}
    (hp : ξ∈cone n δ) (hm : -ξ∈cone n δ) : False := by
  apply no_unit_antipodes (direction ξ) n (direction_norm hp.1) δ hδ hp.2
  simpa only [direction_neg] using hm.2

theorem zero_not_mem_cone (n : V) (δ : ℝ) : (0:V)∉cone n δ := by
  simp [cone]

theorem symmetric_support_zero (a : V → ℂ) (n : V) (δ : ℝ) (hδ : δ≤1)
    (hsym : ∀ ξ, a (-ξ)=starRingEnd ℂ (a ξ))
    (hsupp : Function.support a ⊆ cone n δ) : ∀ ξ, a ξ=0 := by
  intro ξ
  by_contra hh
  have hn : a (-ξ)≠0 := by
    rw [hsym]
    simpa using hh
  exact cone_no_antipodes n δ hδ (hsupp hh) (hsupp hn)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem fourier_reality (f : 𝓢(V, ℂ)) (hr : ∀ x, starRingEnd ℂ (f x)=f x) (ξ : V) :
    𝓕 f (-ξ)=starRingEnd ℂ (𝓕 f ξ) := by
  change 𝓕 (f : V → ℂ) (-ξ)=starRingEnd ℂ (𝓕 (f : V → ℂ) ξ)
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [inner_neg_right, neg_neg, Circle.smul_def, smul_eq_mul, map_mul, hr]
  rw [← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv, inv_inv]

theorem real_schwartz_single_cone_zero (f : 𝓢(V, ℂ)) (n : V) (δ : ℝ) (hδ : δ≤1)
    (hr : ∀ x, starRingEnd ℂ (f x)=f x)
    (hsupp : Function.support (fun ξ => 𝓕 f ξ) ⊆ cone n δ) : f=0 := by
  have hh : 𝓕 f=0 := by
    ext ξ
    exact symmetric_support_zero (fun ξ => 𝓕 f ξ) n δ hδ (fourier_reality f hr) hsupp ξ
  have hi := congrArg (fun g : 𝓢(V, ℂ) => 𝓕⁻ g) hh
  simpa using hi

theorem fourier_postcomp_scalar {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [CompleteSpace H] (f : 𝓢(V, H)) (L : H →L[ℂ] ℂ) (ξ : V) :
    𝓕 (SchwartzMap.postcompCLM L f) ξ = L (𝓕 f ξ) := by
  change 𝓕 (fun x : V => L (f x)) ξ = L (𝓕 (f : V → H) ξ)
  rw [Real.fourier_eq, Real.fourier_eq,
    ← L.integral_comp_comm ((Real.fourierIntegral_convergent_iff ξ).mpr f.integrable)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp [Circle.smul_def]

theorem fourier_vector_reality {ι : Type*} [Fintype ι]
    (f : 𝓢(V, EuclideanSpace ℂ ι)) (hr : ∀ x i, starRingEnd ℂ (f x i)=f x i)
    (ξ : V) (i : ι) : 𝓕 f (-ξ) i=starRingEnd ℂ (𝓕 f ξ i) := by
  let L : EuclideanSpace ℂ ι →L[ℂ] ℂ := PiLp.proj 2 (fun _ : ι => ℂ) i
  have hh := fourier_reality (SchwartzMap.postcompCLM L f) (fun x => hr x i) ξ
  rw [fourier_postcomp_scalar, fourier_postcomp_scalar] at hh
  exact hh

theorem real_vector_schwartz_single_cone_zero {ι : Type*} [Fintype ι]
    (f : 𝓢(V, EuclideanSpace ℂ ι)) (n : V) (δ : ℝ) (hδ : δ≤1)
    (hr : ∀ x i, starRingEnd ℂ (f x i)=f x i)
    (hsupp : Function.support (fun ξ => 𝓕 f ξ) ⊆ cone n δ) : f=0 := by
  ext x i
  let L : EuclideanSpace ℂ ι →L[ℂ] ℂ := PiLp.proj 2 (fun _ : ι => ℂ) i
  let g : 𝓢(V, ℂ) := SchwartzMap.postcompCLM L f
  have hg : g=0 := by
    apply real_schwartz_single_cone_zero g n δ hδ
    · intro y
      exact hr y i
    · intro ξ hξ
      apply hsupp
      intro hz
      change 𝓕 f ξ=0 at hz
      apply hξ
      change 𝓕 (SchwartzMap.postcompCLM L f) ξ=0
      rw [fourier_postcomp_scalar, hz, map_zero]
  have hx := congrArg (fun h : 𝓢(V, ℂ) => h x) hg
  exact hx

end OperatorDerivativeRewrite.Foundation.SingleConeReality
