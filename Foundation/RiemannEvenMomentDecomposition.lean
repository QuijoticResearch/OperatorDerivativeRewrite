import Foundation.RiemannEvenFourierMoment

/-! Exact decomposition and a quantitative bound for the actual full centered
exponential moment, including the translated right integral. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenMomentDecomposition
open RiemannEvenDomain RiemannEvenWeightedTails

theorem actual_centered_moment_split (m : ℕ) (t u B r : ℝ)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hu : r ≤ u) :
    (∫ v : ℝ in Ici 0, |v-u| * Real.exp (B*|v-u|) * weighted m 0 t 0 v) =
      (∫ v : ℝ in 0..(u-r), (u-v)*Real.exp (B*(u-v))*weighted m 0 t 0 v)+
      (∫ v : ℝ in (u-r)..(u+r), |v-u| * Real.exp (B*|v-u|) * weighted m 0 t 0 v)+
      (∫ s : ℝ in Ioi r, s*Real.exp (B*s)*weighted m 0 t 0 (u+s)) := by
  let f : ℝ → ℝ := fun v => |v-u| * Real.exp (B*|v-u|) * weighted m 0 t 0 v
  have hu0 := hr.trans hu
  have hi := actual_centered_exponential_moment_integrable m t u B hu0 hB
  have hright : IntegrableOn f (Ioi (u+r)) := hi.mono_set (by
    intro v hv; change 0 ≤ v; have hv' : u+r < v := hv; linarith)
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (hi.mono_set Ioi_subset_Ici_self) hright
  have hcont : Continuous f := by
    have hw : Continuous (weighted m 0 t 0) := continuous_iff_continuousAt.mpr
      (fun v => (RiemannEvenRealSaddle.weighted_hasDerivAt m t v).continuousAt)
    exact (by fun_prop : Continuous (fun v : ℝ => |v-u| * Real.exp (B*|v-u|))).mul hw
  have hlocal := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 (u-r))
    (hcont.intervalIntegrable (μ := volume) (u-r) (u+r))
  have hleft : (∫ v : ℝ in 0..(u-r), f v) =
      ∫ v : ℝ in 0..(u-r), (u-v)*Real.exp (B*(u-v))*weighted m 0 t 0 v := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc (0 : ℝ) (u-r) := by
      simpa only [uIcc_of_le (sub_nonneg.mpr hu)] using hv
    have hd : |v-u| = u-v := by rw [abs_of_nonpos (by linarith [hv'.2])]; ring
    simp only [f,hd]
  have htrans := (measurePreserving_add_left (volume : Measure ℝ) u).setIntegral_preimage_emb
    (Homeomorph.addLeft u).measurableEmbedding f (Ioi (u+r))
  have hpre : (fun s : ℝ => u+s) ⁻¹' Ioi (u+r) = Ioi r := by
    ext s; simp only [mem_preimage,mem_Ioi]; constructor <;> intro h <;> linarith
  change (∫ s : ℝ in (fun s : ℝ => u+s) ⁻¹' Ioi (u+r), f (u+s)) = _ at htrans
  rw [hpre] at htrans
  have ht : (∫ v : ℝ in Ioi (u+r), f v) =
      ∫ s : ℝ in Ioi r, s*Real.exp (B*s)*weighted m 0 t 0 (u+s) := by
    rw [← htrans]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hs0 : 0 ≤ s := hr.trans (le_of_lt hs)
    simp only [f,show u+s-u = s by ring,abs_of_nonneg hs0]
  change (∫ v : ℝ in Ici 0, f v) = _
  rw [integral_Ici_eq_integral_Ioi,← hsplit,← hlocal,hleft,ht]

theorem exists_actual_full_moment_bound (m : ℕ) (hm : 0 < m) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (B r t u : ℝ), 0 ≤ B → 0 < r → r ≤ 1/2 →
      1 ≤ t → ((2*m : ℕ) : ℝ)+r ≤ u →
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
      (∫ v : ℝ in Ici 0, |v-u| * Real.exp (B*|v-u|) * weighted m 0 t 0 v)/
        (RiemannEvenFlow.flow m t 0).re ≤
      C*u*Real.exp (B*u)*(t*Real.exp (-t*((((2*m : ℕ) : ℝ)+1)^(2*m)-(((2*m : ℕ) : ℝ))^(2*m)))+
        t^2*Real.exp (-t*r^2))+r*Real.exp (B*r)+K*Real.exp (B^2/(2*t)-(t/2)*r^2) := by
  obtain ⟨C,hC,hleft⟩ := exists_normalized_left_weighted_bound m hm
  obtain ⟨K,hK,hright⟩ := exists_normalized_right_weighted_bound m hm
  refine ⟨C,K,hC,hK,?_⟩
  intro B r t u hB hr hrhalf ht hu hmax
  have huN : ((2*m : ℕ) : ℝ) ≤ u := by linarith
  have hur : r ≤ u := by have hn : (0 : ℝ) ≤ ((2*m : ℕ) : ℝ) := Nat.cast_nonneg _; linarith
  have hl := hleft B r t u hB hr hrhalf ht hu hmax
  have hc := normalized_local_weighted_bound m t u B r hB hr.le hur
  have hh := hright B r t u hr.le ht huN hmax
  rw [actual_centered_moment_split m t u B r hB hr.le hur,add_div,add_div]
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannEvenMomentDecomposition
