import Foundation.SPDECountableModes
import Foundation.GaussianTerminalPredictionSpectrum
import Mathlib.Analysis.PSeries

/-! Countable renormalized Wick responses have an exact physical L2 criterion. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.SPDEWickModes
open InfiniteGaussian GaussianTimeSpaceHermite GaussianNumberSectors
open GaussianTerminalPredictionSpectrum

def wickLine (h : CoefficientSpace) (d : ℕ) : Submodule ℝ GaussianL2 :=
  Submodule.span ℝ {(wick h d : GaussianL2)}

def wickComponent (h : CoefficientSpace) (d : ℕ) (c : ℝ) : wickLine h d :=
  ⟨c • (wick h d : GaussianL2), (wickLine h d).smul_mem c (Submodule.subset_span (by simp))⟩

theorem wickLines_orthogonal (h : ℕ → CoefficientSpace)
    (hh : ∀ i j, i≠j → inner ℝ (h i) (h j)=0) (d : ℕ) (hd : 0<d) :
    OrthogonalFamily ℝ (fun i => wickLine (h i) d) (fun i => (wickLine (h i) d).subtypeₗᵢ) := by
  rintro i j hij ⟨a,ha⟩ ⟨b,hb⟩
  obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨s,rfl⟩ := Submodule.mem_span_singleton.mp hb
  simp [inner_smul_left,inner_smul_right,wick_inner,hh i j hij,ne_of_gt hd]

theorem wickSeries_summable_iff (h : ℕ → CoefficientSpace)
    (hh : ∀ i j, i≠j → inner ℝ (h i) (h j)=0) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ) :
    Summable (fun i => c i • (wick (h i) d : GaussianL2)) ↔
      Summable (fun i => (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d) := by
  have ht := (wickLines_orthogonal h hh d hd).summable_iff_norm_sq_summable
    (fun i => wickComponent (h i) d (c i))
  change Summable (fun i => c i • (wick (h i) d : GaussianL2)) ↔
    Summable (fun i => ‖c i • (wick (h i) d : GaussianL2)‖^2) at ht
  simpa only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,GaussianWickContinuity.wick_norm_sq,mul_assoc] using ht

def wickResponse (h : ℕ → CoefficientSpace) (d : ℕ) (c : ℕ → ℝ) : GaussianL2 :=
  ∑' i, c i • (wick (h i) d : GaussianL2)

theorem wickResponse_hasSum (h : ℕ → CoefficientSpace)
    (hh : ∀ i j, i≠j → inner ℝ (h i) (h j)=0) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d)) :
    HasSum (fun i => c i • (wick (h i) d : GaussianL2)) (wickResponse h d c) :=
  ((wickSeries_summable_iff h hh d hd c).mpr hs).hasSum

theorem finite_wick_energy (h : ℕ → CoefficientSpace)
    (hh : ∀ i j, i≠j → inner ℝ (h i) (h j)=0) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ) (s : Finset ℕ) :
    ‖∑ i∈s, c i • (wick (h i) d : GaussianL2)‖^2=
      ∑ i∈s, (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d := by
  have ht := (wickLines_orthogonal h hh d hd).norm_sum (fun i => wickComponent (h i) d (c i)) s
  change ‖∑ i∈s, c i • (wick (h i) d : GaussianL2)‖^2=
    ∑ i∈s, ‖c i • (wick (h i) d : GaussianL2)‖^2 at ht
  simpa only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,GaussianWickContinuity.wick_norm_sq,mul_assoc] using ht

theorem wickResponse_energy (h : ℕ → CoefficientSpace)
    (hh : ∀ i j, i≠j → inner ℝ (h i) (h j)=0) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d)) :
    HasSum (fun i => (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d) (‖wickResponse h d c‖^2) := by
  have ht := (wickResponse_hasSum h hh d hd c hs).norm.pow 2
  change Tendsto (fun s : Finset ℕ => ‖∑ i∈s, c i • (wick (h i) d : GaussianL2)‖^2)
    atTop (𝓝 (‖wickResponse h d c‖^2)) at ht
  change Tendsto (fun s : Finset ℕ => ∑ i∈s, (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d)
    atTop (𝓝 (‖wickResponse h d c‖^2))
  simpa only [finite_wick_energy h hh d hd c] using ht

theorem wickResponse_projection (h : ℕ → CoefficientSpace)
    (hh : ∀ i j, i≠j → inner ℝ (h i) (h j)=0) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d)) (n : ℕ) :
    projection n (wickResponse h d c)=if n=d then wickResponse h d c else 0 := by
  have ht := (projection n).hasSum (wickResponse_hasSum h hh d hd c hs)
  simp only [map_smul,projection_wick] at ht
  by_cases hn : n=d
  · simp only [hn,ite_true] at ht ⊢
    exact ht.unique (wickResponse_hasSum h hh d hd c hs)
  · simp only [hn,ite_false,smul_zero] at ht ⊢
    exact ht.unique hasSum_zero

theorem wickResponse_recovery_graph (h : ℕ → CoefficientSpace)
    (hh : ∀ i j, i≠j → inner ℝ (h i) (h j)=0) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d)) :
    (GaussianDivergenceRecovery.recovery (wickResponse h d c),wickResponse h d c)∈hilbertDivergence.graph := by
  have ht := GaussianDivergenceRecovery.recovery_graph (wickResponse h d c)
  simpa only [wickResponse_projection h hh d hd c hs 0,show (0 : ℕ)≠d by omega,ite_false,sub_zero] using ht

theorem wickResponse_recovery_energy (h : ℕ → CoefficientSpace)
    (hh : ∀ i j, i≠j → inner ℝ (h i) (h j)=0) (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2*(d.factorial : ℝ)*(‖h i‖^2)^d)) :
    ‖GaussianDivergenceRecovery.recovery (wickResponse h d c)‖^2=
      (d : ℝ)⁻¹*‖wickResponse h d c‖^2 := by
  have ht := GaussianDivergenceRecovery.recovery_inverse_energy_hasSum (wickResponse h d c)
  simp only [wickResponse_projection h hh d hd c hs] at ht
  have he (n : ℕ) : (n : ℝ)⁻¹*‖if n=d then wickResponse h d c else 0‖^2=
      if n=d then (d : ℝ)⁻¹*‖wickResponse h d c‖^2 else 0 := by
    split_ifs with hn
    · subst n; rfl
    · simp
  simp_rw [he] at ht
  exact ht.unique (hasSum_ite_eq d _)

attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

def modeDirection (i : ℕ) (v : GaussianTimeHilbert.TimeHilbert) : CoefficientSpace :=
  SeparableHilbertEmbedding.hilbertEmbedding SPDECountableModes.ModeHilbert (SPDECountableModes.modeVector i v)

theorem modeDirections_orthogonal (v : ℕ → GaussianTimeHilbert.TimeHilbert) :
    ∀ i j, i≠j → inner ℝ (modeDirection i (v i)) (modeDirection j (v j))=0 := by
  intro i j hij
  rw [modeDirection,modeDirection,LinearIsometry.inner_map_map,SPDECountableModes.modeVector_inner,if_neg hij]

theorem modeDirection_energy (i : ℕ) (v : GaussianTimeHilbert.TimeHilbert) :
    ‖modeDirection i v‖^2=‖v‖^2 := by
  change ‖SeparableHilbertEmbedding.hilbertEmbedding SPDECountableModes.ModeHilbert
    (SPDECountableModes.modeEmbedding i v)‖^2=‖v‖^2
  rw [LinearIsometry.norm_map,LinearIsometry.norm_map]

def brownianDirection (i : ℕ) (t : ℝ≥0) : CoefficientSpace :=
  modeDirection i (GaussianTimeHilbert.timeVector t)

theorem brownianDirection_energy (i : ℕ) (t : ℝ≥0) : ‖brownianDirection i t‖^2=(t : ℝ) := by
  rw [brownianDirection,modeDirection_energy,GaussianTimeHilbert.timeVector_norm_sq]

def rawSquare (h : CoefficientSpace) : GaussianL2 :=
  (wick h 2 : GaussianL2)+‖h‖^2 • gaussianOne

theorem rawSquare_coeFn (h : CoefficientSpace) :
    rawSquare h =ᵐ[gaussianProduct] fun ω => (firstChaosEmbedding h ω)^2 := by
  filter_upwards [Lp.coeFn_add (wick h 2 : GaussianL2) (‖h‖^2 • gaussianOne),
    Lp.coeFn_smul (‖h‖^2) gaussianOne,gaussianOne_coeFn,core_coeFn h (‖h‖^2) 2] with ω ha hs h1 hw
  change ((wick h 2 : GaussianL2)+‖h‖^2 • gaussianOne) ω=_
  rw [ha,Pi.add_apply,hs,Pi.smul_apply,h1]
  change (wick h 2 : GaussianL2) ω=value 2 (firstChaosEmbedding h ω) (‖h‖^2) at hw
  rw [hw,value_two]
  ring

theorem rawSquare_mean (h : CoefficientSpace) : inner ℝ gaussianOne (rawSquare h)=‖h‖^2 := by
  rw [rawSquare,inner_add_right,inner_smul_right,wick_centered h 1,
    GaussianDeterministicGraphCore.gaussianOne_inner_self]
  simp

theorem rawSquareSeries_mean_obstruction (h : ℕ → CoefficientSpace) (c : ℕ → ℝ)
    (hc : ¬ Summable (fun i => c i*‖h i‖^2)) :
    ¬ Summable (fun i => c i • rawSquare (h i)) := by
  intro hs
  have ht := (innerSL ℝ gaussianOne).hasSum hs.hasSum
  apply hc
  have hh := ht.summable
  change Summable (fun i => inner ℝ gaussianOne (c i • rawSquare (h i))) at hh
  simpa only [inner_smul_right,rawSquare_mean] using hh

def harmonicCoefficient (i : ℕ) : ℝ := 1/((i : ℝ)+1)

theorem harmonic_square_summable : Summable (fun i => (harmonicCoefficient i)^2) := by
  have hs := (_root_.summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : (1 : ℕ)<2))
  simpa only [harmonicCoefficient,one_div_pow,Nat.cast_add,Nat.cast_one] using hs

theorem harmonic_not_summable : ¬ Summable harmonicCoefficient := by
  intro hs
  apply Real.not_summable_one_div_natCast
  apply (_root_.summable_nat_add_iff 1).mp
  change Summable (fun n : ℕ => 1/((n : ℝ)+1)) at hs
  simpa only [Nat.cast_add,Nat.cast_one] using hs

theorem actual_centered_squares_summable :
    Summable (fun i => harmonicCoefficient i • (wick (brownianDirection i 1) 2 : GaussianL2)) := by
  apply (wickSeries_summable_iff (fun i => brownianDirection i 1)
    (modeDirections_orthogonal (fun _ => GaussianTimeHilbert.timeVector 1)) 2 (by norm_num)
    harmonicCoefficient).mpr
  simpa only [brownianDirection_energy,NNReal.coe_one,one_pow,mul_one] using
    harmonic_square_summable.mul_right ((2 : ℕ).factorial : ℝ)

theorem actual_raw_squares_not_summable :
    ¬ Summable (fun i => harmonicCoefficient i • rawSquare (brownianDirection i 1)) := by
  apply rawSquareSeries_mean_obstruction
  simpa only [brownianDirection_energy,NNReal.coe_one,mul_one] using harmonic_not_summable
end OperatorDerivativeRewrite.Foundation.SPDEWickModes




