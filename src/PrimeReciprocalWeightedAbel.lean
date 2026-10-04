import PrimeEulerWeightedTransfer
import MertensPrimeInterval

/-! Increasing weighted sums over an arbitrary finite closed interval of
actual primes. The arithmetic comparison is proved from the existing
reciprocal-prime interval bound; both prime endpoints remain included. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Real MeasureTheory Set
open scoped BigOperators
namespace PrimeReciprocalWeightedAbel
open PrimeEulerWeightedTransfer

def comparison (a b t : ℝ) : ℝ :=
  log (log b)-log (log t)+10/log a

def density (t : ℝ) : ℝ := t⁻¹/log t

theorem comparison_continuous (a b : ℝ) (ha : 1 < a) :
    ContinuousOn (comparison a b) (Icc a b) := by
  have hn : ∀ t ∈ Icc a b, t ≠ 0 := fun t ht => by linarith [ht.1]
  have hl : ∀ t ∈ Icc a b, log t ≠ 0 := fun t ht =>
    (log_pos (ha.trans_le ht.1)).ne'
  exact (continuousOn_const.sub ((continuousOn_id.log hn).log hl)).add
    continuousOn_const

theorem density_continuous (a b : ℝ) (ha : 1 < a) :
    ContinuousOn density (Icc a b) := by
  have hn : ∀ t ∈ Icc a b, t ≠ 0 := fun t ht => by linarith [ht.1]
  have hl : ∀ t ∈ Icc a b, log t ≠ 0 := fun t ht =>
    (log_pos (ha.trans_le ht.1)).ne'
  exact (continuousOn_id.inv₀ hn).div (continuousOn_id.log hn) hl

theorem comparison_deriv (a b t : ℝ) (ht : 1 < t) :
    HasDerivAt (comparison a b) (-density t) t := by
  have hd := (hasDerivAt_log (by linarith : t ≠ 0)).log (log_pos ht).ne'
  convert! ((hasDerivAt_const t (log (log b))).sub hd).add_const (10/log a) using 1
  simp only [density]
  ring

theorem finiteTail_bound (S : Finset ℕ) (a b t : ℝ) (ha : 1 < a)
    (ht : t ∈ Icc a b)
    (hS : ∀ p ∈ S, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ b) :
    finiteTail S (fun p => (p:ℝ)⁻¹) t ≤ comparison a b t := by
  classical
  rw [finiteTail, ← Finset.sum_filter]
  have ht1 : 1 < t := ha.trans_le ht.1
  have hb1 : 1 < b := ht1.trans_le ht.2
  have hm := MertensPrimeInterval.prime_reciprocal_interval t b
    (S.filter (fun p : ℕ => t ≤ (p:ℝ))) ht1 ht.2 (fun p hp => by
      obtain ⟨hpS, hpt⟩ := Finset.mem_filter.mp hp
      exact ⟨(hS p hpS).1, hpt, (hS p hpS).2.2⟩)
  rw [log_div (log_pos hb1).ne' (log_pos ht1).ne'] at hm
  have he : 10/log t ≤ 10/log a :=
    div_le_div_of_nonneg_left (by norm_num) (log_pos ha)
      (log_le_log (by linarith) ht.1)
  unfold comparison
  linarith

theorem weighted_bound (S : Finset ℕ) (a b : ℝ) (φ f : ℝ → ℝ)
    (ha : 1 < a) (hab : a ≤ b)
    (hS : ∀ p ∈ S, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ b)
    (hφa : 0 ≤ φ a) (hφ : ContinuousOn φ (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (hf0 : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt φ (f t) t) :
    (∑ p ∈ S, φ (p:ℝ)*(p:ℝ)⁻¹) ≤
      φ b*(10/log a)+∫ t in a..b, φ t*density t := by
  have hfi : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hf.integrableOn_Icc
  have hci := comparison_continuous a b ha
  have hdi := density_continuous a b ha
  have hI1 : IntervalIntegrable (fun t => f t*comparison a b t) volume a b :=
    hfi.mul_continuousOn (by simpa only [uIcc_of_le hab] using hci)
  have hI2 : IntervalIntegrable (fun t => φ t*density t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (hφ.mul hdi).integrableOn_Icc
  have hrep : ∀ p ∈ S, φ (p:ℝ) = φ a+∫ t in a..(p:ℝ), f t := by
    intro p hp
    have hpa := (hS p hp).2.1
    have hpb := (hS p hp).2.2
    have hsub : Icc a (p:ℝ) ⊆ Icc a b := fun t ht => ⟨ht.1, ht.2.trans hpb⟩
    have hi : IntervalIntegrable f volume a (p:ℝ) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hpa]
      exact (hf.mono hsub).integrableOn_Icc
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpa
      (hφ.mono hsub) (fun t ht => hd t ⟨ht.1, ht.2.trans_le hpb⟩) hi
    linarith
  have hm : (∑ p ∈ S, (p:ℝ)⁻¹) ≤ comparison a b a := by
    have hh := finiteTail_bound S a b a ha ⟨le_rfl, hab⟩ hS
    have heq : finiteTail S (fun p => (p:ℝ)⁻¹) a = ∑ p ∈ S, (p:ℝ)⁻¹ := by
      unfold finiteTail
      apply Finset.sum_congr rfl
      intro p hp
      simp only [ite_eq_left (hS p hp).2.1]
    rwa [heq] at hh
  have hsum : (∑ p ∈ S, φ (p:ℝ)*(p:ℝ)⁻¹) ≤
      φ a*comparison a b a+∫ t in a..b, f t*comparison a b t := by
    rw [weighted_sum_eq_tail_integral S (fun p => (p:ℝ)⁻¹) φ f a b hfi
      (fun p hp => ⟨(hS p hp).2.1, (hS p hp).2.2⟩) hrep]
    apply add_le_add (mul_le_mul_of_nonneg_left hm hφa)
    apply intervalIntegral.integral_mono_on hab
      (mul_finiteTail_intervalIntegrable S (fun p => (p:ℝ)⁻¹) f a b hfi) hI1
    intro t ht
    exact mul_le_mul_of_nonneg_left (finiteTail_bound S a b t ha ht hS) (hf0 t ht)
  have hp : ∀ t ∈ Ioo a b, HasDerivAt (fun x => φ x*comparison a b x)
      (f t*comparison a b t-φ t*density t) t := by
    intro t ht
    convert! (hd t ht).mul (comparison_deriv a b t (ha.trans ht.1)) using 1
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hφ.mul hci) hp (hI1.sub hI2)
  simp only [Pi.mul_apply] at hi
  rw [intervalIntegral.integral_sub hI1 hI2] at hi
  have hc : comparison a b b = 10/log a := by simp [comparison]
  rw [hc] at hi
  linarith

run_cmd do
  for decl in [``comparison_continuous, ``density_continuous, ``comparison_deriv,
      ``finiteTail_bound, ``weighted_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL CLOSED-PRIME WEIGHTED ABEL BOUND CHECKED"
end PrimeReciprocalWeightedAbel
end
