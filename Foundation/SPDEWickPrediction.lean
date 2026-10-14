import Foundation.SPDEWickModes
import Foundation.GaussianWickConditionalProjection
import Foundation.FractionalCurrentObservationObstruction

/-! Conditional predictions of countable renormalized responses survive
loss of orthogonality, with exact finite projected Gram energies. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.SPDEWickPrediction
open InfiniteGaussian GaussianTimeSpaceHermite GaussianNumberSectors GaussianConditionalGraph
open GaussianWickConditionalProjection SPDEWickModes

def gramEnergy (h : ℕ → CoefficientSpace) (d : ℕ) (c : ℕ → ℝ) (s : Finset ℕ) : ℝ :=
  ∑ i∈s, ∑ j∈s, c i*c j*(d.factorial : ℝ)*(inner ℝ (h i) (h j))^d

theorem finite_wick_gram (h : ℕ → CoefficientSpace) (d : ℕ) (c : ℕ → ℝ) (s : Finset ℕ) :
    ‖∑ i∈s, c i • (wick (h i) d : GaussianL2)‖^2=gramEnergy h d c s := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [gramEnergy,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    wick_inner,ite_true]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm (h j) (h i)]
  ring

theorem finite_prediction_gram {I : Type*} (observations : I → CoefficientSpace)
    (h : ℕ → CoefficientSpace) (d : ℕ) (c : ℕ → ℝ) (s : Finset ℕ) :
    ‖conditionalProjection observations (∑ i∈s, c i • (wick (h i) d : GaussianL2))‖^2=
      gramEnergy (fun i => sourceProjection observations (h i)) d c s := by
  simp only [map_sum,map_smul,conditional_wick_projection]
  exact finite_wick_gram _ _ _ _

theorem projected_gram_bounds {I : Type*} (observations : I → CoefficientSpace)
    (h : ℕ → CoefficientSpace) (hh : ∀ i j, i≠j → inner ℝ (h i) (h j)=0)
    (d : ℕ) (hd : 0<d) (c : ℕ → ℝ) (s : Finset ℕ) :
    0≤gramEnergy (fun i => sourceProjection observations (h i)) d c s ∧
      gramEnergy (fun i => sourceProjection observations (h i)) d c s≤
        ∑ i∈s, (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d := by
  rw [← finite_prediction_gram]
  constructor
  · positivity
  · rw [← finite_wick_energy h hh d hd c s]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (conditionalProjection_norm_le observations _)

theorem predicted_response_hasSum {I : Type*} (observations : I → CoefficientSpace)
    (h : ℕ → CoefficientSpace) (hh : ∀ i j, i≠j → inner ℝ (h i) (h j)=0)
    (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d)) :
    HasSum (fun i => c i • (wick (sourceProjection observations (h i)) d : GaussianL2))
      (conditionalProjection observations (wickResponse h d c)) := by
  simpa only [map_smul,conditional_wick_projection] using
    (conditionalProjection observations).hasSum (wickResponse_hasSum h hh d hd c hs)

theorem projected_gram_limit {I : Type*} (observations : I → CoefficientSpace)
    (h : ℕ → CoefficientSpace) (hh : ∀ i j, i≠j → inner ℝ (h i) (h j)=0)
    (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d)) :
    Tendsto (gramEnergy (fun i => sourceProjection observations (h i)) d c)
      atTop (𝓝 (‖conditionalProjection observations (wickResponse h d c)‖^2)) := by
  have ht := (predicted_response_hasSum observations h hh d hd c hs).norm.pow 2
  change Tendsto (fun s : Finset ℕ =>
    ‖∑ i∈s, c i • (wick (sourceProjection observations (h i)) d : GaussianL2)‖^2)
      atTop (𝓝 (‖conditionalProjection observations (wickResponse h d c)‖^2)) at ht
  simpa only [finite_wick_gram] using ht

theorem predicted_response_recovery_graph {I : Type*} (observations : I → CoefficientSpace)
    (h : ℕ → CoefficientSpace) (hh : ∀ i j, i≠j → inner ℝ (h i) (h j)=0)
    (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d)) :
    (GaussianDivergenceRecovery.recovery (conditionalProjection observations (wickResponse h d c)),
      conditionalProjection observations (wickResponse h d c))∈hilbertDivergence.graph := by
  have ht := GaussianDivergenceRecovery.recovery_graph
    (conditionalProjection observations (wickResponse h d c))
  simpa only [projection_conditional_commute,wickResponse_projection h hh d hd c hs 0,
    show (0 : ℕ)≠d by omega,ite_false,map_zero,sub_zero] using ht

theorem two_mode_source_projection (u v : CoefficientSpace) (hu : ‖u‖^2=1) (hv : ‖v‖^2=1)
    (horth : inner ℝ u v=0) :
    sourceProjection (fun _ : Unit => u+v) u=(1/2 : ℝ) • (u+v) ∧
    sourceProjection (fun _ : Unit => u+v) v=(1/2 : ℝ) • (u+v) := by
  have hn : ‖u+v‖^2=2 := by rw [norm_add_sq_real,hu,hv,horth]; ring
  have ho : inner ℝ v u=0 := (real_inner_comm _ _).trans horth
  constructor <;> rw [FractionalCurrentObservationObstruction.source_projection_single,hn,inner_add_left]
  · rw [real_inner_self_eq_norm_sq,hu,ho]; norm_num
  · rw [real_inner_self_eq_norm_sq,hv,horth]; norm_num

theorem two_mode_difference_forecast_zero (u v : CoefficientSpace) (hu : ‖u‖^2=1) (hv : ‖v‖^2=1)
    (horth : inner ℝ u v=0) (d : ℕ) :
    conditionalProjection (fun _ : Unit => u+v)
      ((wick u d : GaussianL2)-(wick v d : GaussianL2))=0 := by
  obtain ⟨hp,hq⟩ := two_mode_source_projection u v hu hv horth
  rw [map_sub,conditional_wick_projection,conditional_wick_projection,hp,hq,sub_self]

theorem two_mode_sum_forecast_energy (u v : CoefficientSpace) (hu : ‖u‖^2=1) (hv : ‖v‖^2=1)
    (horth : inner ℝ u v=0) (d : ℕ) :
    ‖conditionalProjection (fun _ : Unit => u+v)
      ((wick u d : GaussianL2)+(wick v d : GaussianL2))‖^2=
        4*(d.factorial : ℝ)*(1/2 : ℝ)^d := by
  obtain ⟨hp,hq⟩ := two_mode_source_projection u v hu hv horth
  have hn : ‖u+v‖^2=2 := by rw [norm_add_sq_real,hu,hv,horth]; ring
  rw [map_add,conditional_wick_projection,conditional_wick_projection,hp,hq,
    ← two_smul ℝ (wick ((1/2 : ℝ) • (u+v)) d : GaussianL2),norm_smul,mul_pow,
    GaussianWickContinuity.wick_norm_sq,norm_smul,mul_pow]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<2),
    abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  rw [hn]
  norm_num
  ring

theorem actual_brownian_square_forecast_energy :
    ‖conditionalProjection (fun _ : Unit => brownianDirection 0 1+brownianDirection 1 1)
      ((wick (brownianDirection 0 1) 2 : GaussianL2)+(wick (brownianDirection 1 1) 2 : GaussianL2))‖^2=2 := by
  have hu : ‖brownianDirection 0 1‖^2=1 := by simpa using brownianDirection_energy 0 1
  have hv : ‖brownianDirection 1 1‖^2=1 := by simpa using brownianDirection_energy 1 1
  have ho : inner ℝ (brownianDirection 0 1) (brownianDirection 1 1)=0 :=
    modeDirections_orthogonal (fun _ => GaussianTimeHilbert.timeVector 1) 0 1 (by decide)
  have ht := two_mode_sum_forecast_energy _ _ hu hv ho 2
  norm_num at ht
  simpa only [map_add] using ht
end OperatorDerivativeRewrite.Foundation.SPDEWickPrediction



