import PairSpacingCollectedEnergy
import PairSpacingRationalMeanSquare
import PairFourierProjection

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos374.PairSpacingProjectionSum

open PairSpacingRational PairSpacingKernel PairSpacingMeanSquare PairSpacingCollectedEnergy PairFourier
theorem phase_eq_kernel (n : ℕ) (k : ℤ) (x : ℝ) :
    phase n k x = exponentialKernel (angularFrequency (n,k)) x := by
  simp only [phase, fourier_coe_apply, exponentialKernel, angularFrequency, frequency,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_intCast,
    Complex.ofReal_ofNat]
  congr 1
  ring

theorem representative_fiber (Q F n : ℕ) (hn : n ∈ Finset.Icc 1 Q) :
    (representatives Q F).filter (fun p => p.1 = n) =
      ((hardModes n F).erase 0).image (fun k => (n,k)) := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpR, hpn⟩
    have hp' := mem_representatives hpR
    apply Finset.mem_image.mpr
    refine ⟨p.2, Finset.mem_erase.mpr ⟨hp'.2.2.1, ?_⟩, ?_⟩
    · have hh := abs_le.mp hp'.2.2.2
      simpa only [hardModes, Finset.mem_Icc, hpn] using hh
    · exact Prod.ext hpn.symm rfl
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    rcases Finset.mem_erase.mp hk with ⟨hk0, hk⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_representatives_iff.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2, hk0, ?_⟩, rfl⟩
    exact abs_le.mpr (Finset.mem_Icc.mp hk)

theorem hard_sum_eq_representative_sum (Q : ℕ) (a : ℕ → ℝ) (h : ℝ) (F : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 Q, (a n : ℂ) * (if hn : 0 < n then hardProjection n hn h F x else 0)) =
      exponentialSum (representatives Q F) (representationCoefficient a h) angularFrequency x := by
  unfold exponentialSum
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun p (hp : p ∈ representatives Q F) =>
      Finset.mem_Icc.mpr ⟨(mem_representatives hp).1, (mem_representatives hp).2.1⟩)
    (fun p => representationCoefficient a h p * exponentialKernel (angularFrequency p) x)]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  rw [representative_fiber Q F n hn, Finset.sum_image]
  · simp only [dite_eq_left hn0, hardProjection, projection, representationCoefficient,
      divisorCoefficient, ← phase_eq_kernel]
    rw [Finset.mul_sum]
    have hzero : (0 : ℤ) ∈ hardModes n F := by
      simp only [hardModes, Finset.mem_Icc]
      constructor <;> omega
    rw [← Finset.sum_erase_add (hardModes n F)
      (fun k => (a n : ℂ) * (fourierCoeffOn
        (show (0 : ℝ) < n from by exact_mod_cast hn0) (discrepancy n h) k * phase n k x)) hzero]
    rw [coefficient_zero hn0 h]
    simp only [zero_mul, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · intro k hk l hl he
    exact congrArg Prod.snd he


end Erdos374.PairSpacingProjectionSum

