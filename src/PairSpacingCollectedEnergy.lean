import PairCommonModes
import PairFourierTransport
import PairFourierProjection
import PairProjectionEnergy
import PairSpacingMeanSquare

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos374.PairSpacingCollectedEnergy

open PairSpacingRational PairSpacingMeanSquare PairCommonModes PairCommonPeriod PairFourier

def divisorCoefficient (n : ℕ) (h : ℝ) (k : ℤ) : ℂ :=
  if hn : 0 < n then fourierCoeffOn (show (0 : ℝ) < n from by exact_mod_cast hn)
    (discrepancy n h) k else 0

def representationCoefficient (a : ℕ → ℝ) (h : ℝ) (p : ℕ × ℤ) : ℂ :=
  (a p.1 : ℂ) * divisorCoefficient p.1 h p.2

def coefficient (Q F : ℕ) (a : ℕ → ℝ) (h ξ : ℝ) : ℂ :=
  collectedCoefficient (representatives Q F) (representationCoefficient a h) frequency ξ

theorem remainder_eq_sum (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) :
    PairProjectionEnergy.remainder Q a h =
      fun x => ∑ n ∈ Finset.Icc 1 Q, (a n : ℂ) * discrepancy n h x := by
  funext x
  simp only [PairProjectionEnergy.remainder, SingletonResidueVariance.remainder,
    Complex.ofReal_sum, Complex.ofReal_mul, discrepancy]

theorem common_coefficient_eq_collection (Q F : ℕ) (a : ℕ → ℝ) (h : ℝ)
    (K : ℤ) (hK : K ∈ PairCommonModes.modes Q F) :
    fourierCoeffOn
      (show (0 : ℝ) < period Q from by exact_mod_cast period_pos Q)
      (PairProjectionEnergy.remainder Q a h) K =
      ∑ p ∈ (representatives Q F).filter (fun p => commonMode Q p = K),
        representationCoefficient a h p := by
  have hP : (0 : ℝ) < period Q := by exact_mod_cast period_pos Q
  rw [remainder_eq_sum, coefficient_sum (period Q : ℝ) hP (Finset.Icc 1 Q)]
  · rw [← Finset.sum_fiberwise_of_maps_to
      (fun p (hp : p ∈ (representatives Q F).filter (fun p => commonMode Q p = K)) =>
        Finset.mem_Icc.mpr ⟨(mem_representatives (Finset.mem_filter.mp hp).1).1,
          (mem_representatives (Finset.mem_filter.mp hp).1).2.1⟩)
      (representationCoefficient a h)]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hm0 := multiplier_pos hn
    have hmZ : (multiplier Q n : ℤ) ≠ 0 := by exact_mod_cast hm0.ne'
    have hperiod : (multiplier Q n : ℝ) * (n : ℝ) = period Q := by
      exact_mod_cast multiplier_mul hn
    rw [fourierCoeffOn.const_mul]
    by_cases hd : (multiplier Q n : ℤ) ∣ K
    · obtain ⟨k, hk⟩ := hd
      have hnk : (n, k) ∈ representatives Q F :=
        compatible_mem_representatives hK hn hk.symm
      have htransport := PairFourierTransport.coefficient_mul_period (n : ℝ) hnR
        (multiplier Q n) hm0 (discrepancy n h) (discrepancy_periodic n hn0 h)
        (discrepancy_intervalIntegrable n h) k
      simp only [hperiod] at htransport
      rw [hk, htransport]
      rw [Finset.sum_eq_single (n, k)]
      · simp only [representationCoefficient, divisorCoefficient, dite_eq_left hn0]
      · intro p hp hpnk
        rcases Finset.mem_filter.mp hp with ⟨hpK, hpn⟩
        rcases Finset.mem_filter.mp hpK with ⟨hpR, hpK⟩
        have he : p = (n,k) := by
          apply Prod.ext hpn
          have heq : (multiplier Q n : ℤ) * p.2 = (multiplier Q n : ℤ) * k := by
            simpa only [commonMode, hpn, hk] using hpK
          exact mul_left_cancel₀ hmZ heq
        exact False.elim (hpnk he)
      · intro hnmem
        exact False.elim (hnmem (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hnk, by simp only [commonMode]⟩, rfl⟩))
    · have htransport := PairFourierTransport.coefficient_eq_zero_of_not_dvd
        (n : ℝ) hnR (multiplier Q n) hm0 (discrepancy n h)
        (discrepancy_periodic n hn0 h) K hd
      simp only [hperiod] at htransport
      rw [htransport, mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpK, hpn⟩
      rcases Finset.mem_filter.mp hpK with ⟨hpR, hpK⟩
      apply False.elim
      apply hd
      refine ⟨p.2, ?_⟩
      simpa only [commonMode, hpn] using hpK.symm
  · intro n hn
    exact (discrepancy_intervalIntegrable n h 0 _).const_mul _

def commonIndex (Q : ℕ) (ξ : ℝ) : ℤ := ⌊(period Q : ℝ) * ξ⌋

theorem commonIndex_frequency {Q : ℕ} (p : ℕ × ℤ)
    (hn : p.1 ∈ Finset.Icc 1 Q) :
    commonIndex Q (frequency p) = commonMode Q p := by
  rw [commonIndex, ← commonMode_frequency p hn, Int.floor_intCast]

theorem commonIndex_cast {Q F : ℕ} {ξ : ℝ} (hξ : ξ ∈ frequencies Q F) :
    (commonIndex Q ξ : ℝ) = (period Q : ℝ) * ξ := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hξ
  have hp' := mem_representatives hp
  have hn := Finset.mem_Icc.mpr ⟨hp'.1, hp'.2.1⟩
  rw [commonIndex_frequency p hn, commonMode_frequency p hn]

theorem commonIndex_injOn (Q F : ℕ) :
    Set.InjOn (commonIndex Q) (frequencies Q F : Set ℝ) := by
  intro ξ hξ η hη he
  have hc := congrArg (fun k : ℤ => (k : ℝ)) he
  rw [commonIndex_cast hξ, commonIndex_cast hη] at hc
  exact mul_left_cancel₀ (by exact_mod_cast (period_pos Q).ne') hc

theorem coefficient_eq_common (Q F : ℕ) (a : ℕ → ℝ) (h ξ : ℝ)
    (hξ : ξ ∈ frequencies Q F) :
    coefficient Q F a h ξ =
      fourierCoeffOn (show (0 : ℝ) < period Q from by exact_mod_cast period_pos Q)
        (PairProjectionEnergy.remainder Q a h) (commonIndex Q ξ) := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hξ
  have hp' := mem_representatives hp
  have hn := Finset.mem_Icc.mpr ⟨hp'.1, hp'.2.1⟩
  rw [commonIndex_frequency p hn, common_coefficient_eq_collection Q F a h _
    (Finset.mem_image_of_mem (commonMode Q) hp)]
  unfold coefficient collectedCoefficient
  congr 1
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hq, he⟩
    have hq' := mem_representatives hq
    exact ⟨hq, (same_commonMode_iff q p
      (Finset.mem_Icc.mpr ⟨hq'.1, hq'.2.1⟩) hn).mpr he⟩
  · rintro ⟨hq, he⟩
    have hq' := mem_representatives hq
    exact ⟨hq, (same_commonMode_iff q p
      (Finset.mem_Icc.mpr ⟨hq'.1, hq'.2.1⟩) hn).mp he⟩

theorem energy_le (Q F : ℕ) (a : ℕ → ℝ) (B h : ℝ)
    (hB : 0 ≤ B) (hh : 0 ≤ h)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (∑ ξ ∈ frequencies Q F, ‖coefficient Q F a h ξ‖ ^ 2) ≤
      B ^ 2 * h * SingletonHarmonic.harmonicSum Q ^ 3 := by
  have hb := PairProjectionEnergy.energy_le Q a B h hB hh ha
    ((frequencies Q F).image (commonIndex Q))
  rw [Finset.sum_image (commonIndex_injOn Q F)] at hb
  convert hb using 1
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [coefficient_eq_common Q F a h ξ hξ]

end Erdos374.PairSpacingCollectedEnergy

