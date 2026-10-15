import Foundation.SPDEExponentialForcing
import Foundation.GaussianLinearFieldDivergenceCompletion
import Foundation.GaussianRecoveryCompactnessObstruction

/-! Actual Hilbert-valued damped forcing and its completed quadratic source divergence. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.SPDEHilbertExponentialForcing
open InfiniteGaussian GaussianTimeHilbert SPDECountableModes GaussianTimeFieldNorm
open GaussianLinearFieldDivergenceCompletion SPDEExponentialForcing
open GaussianNumberSectors GaussianDivergenceRecovery GaussianSourceHodge
attribute [local instance] timeHilbert_secondCountable

def unitDirection (n : ℕ) : CoefficientSpace := lp.single 2 n (1 : ℝ)

theorem unitDirection_norm (n : ℕ) : ‖unitDirection n‖=1 :=
  GaussianRecoveryCompactnessObstruction.coefficient_single_orthonormal.norm_eq_one n

def spatialEmbedding (n : ℕ) : GaussianL2 →ₗᵢ[ℝ] GaussianVectorL2 where
  __ := (scalarTensor (unitDirection n)).toLinearMap
  norm_map' f := by
    have he : ‖scalarTensor (unitDirection n) f‖^2=‖f‖^2 := by
      rw [← real_inner_self_eq_norm_sq,scalarTensor_pair_inner,real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq,unitDirection_norm,one_pow,mul_one]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by decide : (2 : ℕ)≠0)).mp he

theorem spatialEmbedding_inner (i j : ℕ) (f g : GaussianL2) :
    inner ℝ (spatialEmbedding i f) (spatialEmbedding j g)=if i=j then inner ℝ f g else 0 := by
  change inner ℝ (scalarTensor (unitDirection i) f) (scalarTensor (unitDirection j) g)=_
  rw [scalarTensor_pair_inner]
  have hc := orthonormal_iff_ite.mp GaussianRecoveryCompactnessObstruction.coefficient_single_orthonormal
  change inner ℝ f g*inner ℝ (lp.single 2 i (1 : ℝ) : CoefficientSpace) (lp.single 2 j (1 : ℝ))=_
  rw [hc i j]
  by_cases hij : i=j <;> simp [hij]

def spatialMode (n : ℕ) : TimeHilbert →ₗᵢ[ℝ] GaussianVectorL2 := (spatialEmbedding n).comp (gaussianMode n)

theorem spatialModes_orthogonal : OrthogonalFamily ℝ (fun _ : ℕ => TimeHilbert) spatialMode := by
  intro i j hij v w
  change inner ℝ (spatialEmbedding i (gaussianMode i v)) (spatialEmbedding j (gaussianMode j w))=0
  rw [spatialEmbedding_inner,if_neg hij]

theorem spatialSeries_summable_iff (c : ℕ → ℝ) (v : ℕ → TimeHilbert) :
    Summable (fun n => c n • spatialMode n (v n)) ↔ Summable (fun n => (c n)^2*‖v n‖^2) := by
  simpa only [map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs] using
    spatialModes_orthogonal.summable_iff_norm_sq_summable (fun n => c n • v n)

def spatialResponse (c : ℕ → ℝ) (v : ℕ → TimeHilbert) : GaussianVectorL2 := ∑' n, c n • spatialMode n (v n)

theorem spatialResponse_hasSum (c : ℕ → ℝ) (v : ℕ → TimeHilbert)
    (hs : Summable (fun n => (c n)^2*‖v n‖^2)) :
    HasSum (fun n => c n • spatialMode n (v n)) (spatialResponse c v) :=
  ((spatialSeries_summable_iff c v).mpr hs).hasSum

theorem spatialResponse_energy (c : ℕ → ℝ) (v : ℕ → TimeHilbert)
    (hs : Summable (fun n => (c n)^2*‖v n‖^2)) : HasSum (fun n => (c n)^2*‖v n‖^2) (‖spatialResponse c v‖^2) := by
  have ht := (spatialResponse_hasSum c v hs).norm.pow 2
  change Tendsto (fun s : Finset ℕ => ‖∑ n ∈ s, c n • spatialMode n (v n)‖^2) atTop (𝓝 (‖spatialResponse c v‖^2)) at ht
  change Tendsto (fun s : Finset ℕ => ∑ n ∈ s, (c n)^2*‖v n‖^2) atTop (𝓝 (‖spatialResponse c v‖^2))
  have he (s : Finset ℕ) : ‖∑ n ∈ s, c n • spatialMode n (v n)‖^2=∑ n ∈ s, (c n)^2*‖v n‖^2 := by
    simpa only [map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs] using
      spatialModes_orthogonal.norm_sum (fun n => c n • v n) s
  simpa only [he] using ht

def spatialCoordinate (n : ℕ) : GaussianVectorL2 →L[ℝ] GaussianL2 :=
  (innerSL ℝ (unitDirection n)).compLpL 2 gaussianProduct

theorem spatialCoordinate_tensor (n : ℕ) (u : CoefficientSpace) (f : GaussianL2) :
    spatialCoordinate n (scalarTensor u f)=inner ℝ (unitDirection n) u • f := by
  apply Lp.ext
  filter_upwards [(innerSL ℝ (unitDirection n)).coeFn_compLpL (scalarTensor u f),scalarTensor_coeFn u f,
    Lp.coeFn_smul (inner ℝ (unitDirection n) u) f] with ω hm ht hs
  change (((innerSL ℝ (unitDirection n)).compLpL 2 gaussianProduct) (scalarTensor u f)) ω=_
  rw [hm,ht,hs,Pi.smul_apply]
  change inner ℝ (unitDirection n) (f ω • u)=inner ℝ (unitDirection n) u*f ω
  rw [real_inner_smul_right,mul_comm]

theorem spatialCoordinate_mode (n m : ℕ) (v : TimeHilbert) :
    spatialCoordinate n (spatialMode m v)=if n=m then gaussianMode m v else 0 := by
  change spatialCoordinate n (scalarTensor (unitDirection m) (gaussianMode m v))=_
  rw [spatialCoordinate_tensor]
  have hc := orthonormal_iff_ite.mp GaussianRecoveryCompactnessObstruction.coefficient_single_orthonormal
  change inner ℝ (lp.single 2 n (1 : ℝ) : CoefficientSpace) (lp.single 2 m (1 : ℝ)) • gaussianMode m v=_
  rw [hc n m]
  by_cases hnm : n=m <;> simp [hnm]

theorem spatialResponse_coordinate (c : ℕ → ℝ) (v : ℕ → TimeHilbert)
    (hs : Summable (fun n => (c n)^2*‖v n‖^2)) (n : ℕ) :
    spatialCoordinate n (spatialResponse c v)=c n • gaussianMode n (v n) := by
  have ht := (spatialCoordinate n).hasSum (spatialResponse_hasSum c v hs)
  change HasSum (fun m => spatialCoordinate n (c m • spatialMode m (v m))) (spatialCoordinate n (spatialResponse c v)) at ht
  simp only [map_smul,spatialCoordinate_mode] at ht
  have hh : HasSum (fun m => c m • (if n=m then gaussianMode m (v m) else 0)) (c n • gaussianMode n (v n)) := by
    have he : c n • (if n=n then gaussianMode n (v n) else 0)=c n • gaussianMode n (v n) := by simp
    rw [← he]
    apply hasSum_single n
    intro m hmn
    simp [Ne.symm hmn]
  exact ht.unique hh

theorem spatialResponse_coeFn_coordinate (c : ℕ → ℝ) (v : ℕ → TimeHilbert)
    (hs : Summable (fun n => (c n)^2*‖v n‖^2)) (n : ℕ) :
    (fun ω => spatialResponse c v ω n) =ᵐ[gaussianProduct] fun ω => c n*gaussianMode n (v n) ω := by
  have hm := (innerSL ℝ (unitDirection n)).coeFn_compLpL (spatialResponse c v)
  change spatialCoordinate n (spatialResponse c v) =ᵐ[gaussianProduct]
    fun ω => inner ℝ (unitDirection n) (spatialResponse c v ω) at hm
  rw [spatialResponse_coordinate c v hs n] at hm
  filter_upwards [hm,Lp.coeFn_smul (c n) (gaussianMode n (v n))] with ω hi hc
  rw [hc,Pi.smul_apply,smul_eq_mul] at hi
  simpa only [unitDirection,lp.inner_single_left,Real.inner_apply,one_mul] using hi.symm

theorem spatialResponse_linear (c : ℕ → ℝ) (v : ℕ → TimeHilbert)
    (hs : Summable (fun n => (c n)^2*‖v n‖^2)) : spatialResponse c v∈linearGaussianFields := by
  have hm (n : ℕ) : spatialMode n (v n)∈linearGaussianFields := by
    change scalarTensor (unitDirection n) (firstChaosEmbedding (SPDEWickModes.modeDirection n (v n)))∈linearGaussianFields
    exact linear_rank_mem _ _
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (spatialResponse_hasSum c v hs)
  exact Eventually.of_forall fun s => linearGaussianFields.sum_mem (fun n hn => linearGaussianFields.smul_mem _ (hm n))

def exponentialField (rate : ℕ → ℝ≥0) (c : ℕ → ℝ) (t : ℝ≥0) : GaussianVectorL2 :=
  spatialResponse c (fun n => responseVector (rate n) t)

theorem exponential_field_trace_iff (rate : ℕ → ℝ≥0) (hrate : ∀ n,1≤rate n)
    (c : ℕ → ℝ) (t : ℝ≥0) (ht : 0<t) :
    Summable (fun n => c n • spatialMode n (responseVector (rate n) t)) ↔
      Summable (fun n => (c n)^2/(rate n : ℝ)) := by
  rw [spatialSeries_summable_iff,reciprocal_trace_summable_iff rate hrate c t ht]

theorem exponential_field_energy (rate : ℕ → ℝ≥0) (hrate : ∀ n,1≤rate n)
    (c : ℕ → ℝ) (t : ℝ≥0) (ht : 0<t) (hs : Summable (fun n => (c n)^2/(rate n : ℝ))) :
    HasSum (fun n => (c n)^2*(1-Real.exp (-2*(rate n : ℝ)*(t : ℝ)))/(2*(rate n : ℝ)))
      (‖exponentialField rate c t‖^2) := by
  have hv := (reciprocal_trace_summable_iff rate hrate c t ht).mpr hs
  have he := spatialResponse_energy c (fun n => responseVector (rate n) t) hv
  have hf (n : ℕ) : ‖responseVector (rate n) t‖^2=
      (1-Real.exp (-2*(rate n : ℝ)*(t : ℝ)))/(2*(rate n : ℝ)) :=
    responseVector_energy_exact (rate n) t (by linarith [hrate n])
  simpa only [hf,mul_div_assoc,exponentialField] using he

theorem exponential_field_divergence (rate : ℕ → ℝ≥0) (hrate : ∀ n,1≤rate n)
    (c : ℕ → ℝ) (t : ℝ≥0) (ht : 0<t) (hs : Summable (fun n => (c n)^2/(rate n : ℝ))) :
    (exponentialField rate c t,completedDivergence (exponentialField rate c t))∈hilbertDivergence.graph :=
  full_divergence_graph (spatialResponse_linear c (fun n => responseVector (rate n) t)
    ((reciprocal_trace_summable_iff rate hrate c t ht).mpr hs))

theorem exponential_field_quadratic_controls (rate : ℕ → ℝ≥0) (hrate : ∀ n,1≤rate n)
    (c : ℕ → ℝ) (t : ℝ≥0) (ht : 0<t) (hs : Summable (fun n => (c n)^2/(rate n : ℝ))) :
    completedDivergence (exponentialField rate c t)∈sector 2 ∧
      recovery (completedDivergence (exponentialField rate c t))=gradientProjection (exponentialField rate c t) ∧
      ‖completedDivergence (exponentialField rate c t)‖≤Real.sqrt 2*‖exponentialField rate c t‖ := by
  have hm := spatialResponse_linear c (fun n => responseVector (rate n) t)
    ((reciprocal_trace_summable_iff rate hrate c t ht).mpr hs)
  exact ⟨completedDivergence_mem_sector_two hm,completed_recovery hm,completed_norm_bound hm⟩

def quadraticField (t : ℝ≥0) : GaussianVectorL2 := exponentialField quadraticRates (fun _ => 1) t

theorem quadraticField_hasSum (t : ℝ≥0) (ht : 0<t) :
    HasSum (fun n => spatialMode n (responseVector (quadraticRates n) t)) (quadraticField t) := by
  have hs : Summable (fun n => (1 : ℝ)^2/(quadraticRates n : ℝ)) := by simpa using quadratic_trace_summable
  have hv := (reciprocal_trace_summable_iff quadraticRates quadraticRates_lower (fun _ => 1) t ht).mpr hs
  simpa only [one_smul,quadraticField,exponentialField] using
    spatialResponse_hasSum (fun _ => 1) (fun n => responseVector (quadraticRates n) t) hv

theorem quadraticField_divergence_graph (t : ℝ≥0) (ht : 0<t) :
    (quadraticField t,completedDivergence (quadraticField t))∈hilbertDivergence.graph :=
  exponential_field_divergence quadraticRates quadraticRates_lower (fun _ => 1) t ht
    (by simpa using quadratic_trace_summable)

theorem linear_field_series_not_summable (t : ℝ≥0) (ht : 0<t) :
    ¬ Summable (fun n => spatialMode n (responseVector (linearRates n) t)) := by
  intro hs
  have hr (n : ℕ) : 1≤linearRates n := by simp [linearRates]
  have hh := (exponential_field_trace_iff linearRates hr (fun _ => 1) t ht).mp (by simpa only [one_smul] using hs)
  apply SPDEWickModes.harmonic_not_summable
  change Summable (fun n : ℕ => 1/((n : ℝ)+1))
  simpa [linearRates] using hh

end OperatorDerivativeRewrite.Foundation.SPDEHilbertExponentialForcing
