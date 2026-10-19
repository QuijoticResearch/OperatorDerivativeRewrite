import Foundation.RiemannQuarticArithmeticJets

/-! Actual three real Fourier channels, including their monomial factors. -/
noncomputable section
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticChannelJets
open RiemannQuarticDyadic RiemannQuarticTaylorJets RiemannQuarticTrigJets
open RiemannQuarticIntervalJets RiemannQuarticRealCertificate

def monomialJet (U : Box) (m p n : ℕ) : Box :=
  divNat (mul (rational (m.descFactorial n : ℚ) p) (pow U p (m-n)) p) n.factorial p

theorem monomialJet_mem {u : ℝ} {U : Box} (hu : u ∈ U) (m p n : ℕ) :
    coefficient (fun v => v^m) n u ∈ monomialJet U m p n := by
  unfold coefficient
  rw [iteratedDeriv_pow]
  have hc : (m.descFactorial n : ℝ) ∈ rational (m.descFactorial n : ℚ) p := by
    simpa only [Rat.cast_natCast] using rational_mem (m.descFactorial n : ℚ) p
  exact divNat_mem (mul_mem hc (pow_mem hu p (m-n)) p) n.factorial p

private theorem coefficient_neg (f : ℝ → ℝ) (n : ℕ) (u : ℝ) :
    coefficient (fun v => -f v) n u = -coefficient f n u := by
  simp only [coefficient, iteratedDeriv_fun_neg]
  ring

def channelJet (U X : Box) (J : Box × Box) (k p n : ℕ) : Box :=
  match k with
  | 0 => cosJet X J p n
  | 1 => neg (convolution (fun i => monomialJet U 1 p i) (fun i => sinJet X J p i) p n)
  | _ => neg (convolution (fun i => monomialJet U 2 p i) (fun i => cosJet X J p i) p n)

theorem channelJet_mem {x u : ℝ} {U X : Box} {J : Box × Box}
    (hx : x ∈ X) (hu : u ∈ U) (hc : Real.cos (x*u) ∈ J.1) (hs : Real.sin (x*u) ∈ J.2)
    (k p n : ℕ) (hk : k ≤ 2) : coefficient (channel k x) n u ∈ channelJet U X J k p n := by
  interval_cases k
  · have heq : channel 0 x=fun v => Real.cos (x*v) := by
      funext v
      simp only [channel, mul_comm]
    rw [heq]
    exact cosJet_mem hx hc hs p n
  · have heq : channel 1 x=fun v => -(v^1*Real.sin (x*v)) := by
      funext v
      simp only [channel, pow_one, neg_mul, mul_comm v x]
    rw [heq, coefficient_neg]
    exact neg_mem (convolution_mem (fun v : ℝ => v^1) (fun v => Real.sin (x*v))
      (by fun_prop) (by fun_prop) u
      (fun i => monomialJet U 1 p i) (fun i => sinJet X J p i) p n
      (fun i _ => monomialJet_mem hu 1 p i) (fun i _ => sinJet_mem hx hc hs p i))
  · have heq : channel 2 x=fun v => -(v^2*Real.cos (x*v)) := by
      funext v
      simp only [channel, neg_mul, mul_comm v x]
    rw [heq, coefficient_neg]
    exact neg_mem (convolution_mem (fun v : ℝ => v^2) (fun v => Real.cos (x*v))
      (by fun_prop) (by fun_prop) u
      (fun i => monomialJet U 2 p i) (fun i => cosJet X J p i) p n
      (fun i _ => monomialJet_mem hu 2 p i) (fun i _ => cosJet_mem hx hc hs p i))

def integrandJet (U X : Box) (J : Box × Box) (W : ℕ → Box) (k p n : ℕ) : Box :=
  convolution W (fun i => channelJet U X J k p i) p n

theorem integrandJet_mem {x u : ℝ} {U X : Box} {J : Box × Box}
    (hx : x ∈ X) (hu : u ∈ U) (hc : Real.cos (x*u) ∈ J.1) (hs : Real.sin (x*u) ∈ J.2)
    (N k p n : ℕ) (hk : k ≤ 2) (W : ℕ → Box)
    (hW : ∀ i ≤ n, coefficient (RiemannQuarticArithmeticJets.weight N) i u ∈ W i) :
    coefficient (realIntegrand N k x) n u ∈ integrandJet U X J W k p n := by
  exact RiemannQuarticArithmeticJets.realIntegrandJet_mem N k n p x u W
    (fun i => channelJet U X J k p i) hW
    (fun i _ => channelJet_mem hx hu hc hs k p i hk)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticChannelJets
