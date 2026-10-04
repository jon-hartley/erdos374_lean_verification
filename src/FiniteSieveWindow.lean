import Erdos374_Update152
import HarmanDivisorWindow

/-! Finite open-left prime windows from the seed Buchstab identity. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators

namespace FiniteSieveWindow
open Erdos374.HarmanAnalytic151

def window (left x : ℝ) : Finset ℕ := Finset.Ioc ⌊left⌋₊ ⌊x⌋₊

def primeWindow (left x : ℝ) : Finset ℕ := (window left x).filter Nat.Prime

def topCutoff (x : ℝ) : ℕ := Nat.sqrt ⌊x⌋₊ + 1

theorem rough_iff_prime (N n : ℕ) (hN : 1 ≤ N)
    (hnlow : Nat.sqrt N < n) (hnup : n ≤ N) :
    Rough (Nat.sqrt N + 1) n ↔ n.Prime := by
  have hsq : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr (by omega)
  have hn2 : 2 ≤ n := by omega
  constructor
  · intro hrough
    apply Nat.prime_def_le_sqrt.mpr
    constructor
    · exact hn2
    · intro m hm hmsqrt hmdiv
      obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd
        (by omega : m ≠ 1)
      have hple : p ≤ m := Nat.le_of_dvd (by omega : 0 < m) hpm
      have hmsqrtN : m ≤ Nat.sqrt N :=
        hmsqrt.trans (Nat.sqrt_le_sqrt hnup)
      exact hrough p hp (by omega) (dvd_trans hpm hmdiv)
  · intro hnprime p hp hpc hpdiv
    have hpn : p = n := (Nat.prime_dvd_prime_iff_eq hp hnprime).mp hpdiv
    omega

theorem sifted_top_eq_primeWindow (left x : ℝ)
    (hleft : 1 ≤ left) (hlex : left ≤ x)
    (hsqrt : Nat.sqrt ⌊x⌋₊ ≤ ⌊left⌋₊) :
    sifted (window left x) (topCutoff x) = primeWindow left x := by
  have hfloorleft : 1 ≤ ⌊left⌋₊ :=
    (Nat.le_floor_iff (by linarith)).mpr (by norm_num; exact hleft)
  have hxone : 1 ≤ x := hleft.trans hlex
  have hfloorx : 1 ≤ ⌊x⌋₊ :=
    (Nat.le_floor_iff (by linarith)).mpr (by norm_num; exact hxone)
  ext n
  simp only [sifted, primeWindow, Finset.mem_filter]
  constructor
  · rintro ⟨hn, hrough⟩
    have hb := Finset.mem_Ioc.mp hn
    exact ⟨hn, (rough_iff_prime ⌊x⌋₊ n hfloorx
      (by omega) hb.2).mp hrough⟩
  · rintro ⟨hn, hprime⟩
    have hb := Finset.mem_Ioc.mp hn
    exact ⟨hn, (rough_iff_prime ⌊x⌋₊ n hfloorx
      (by omega) hb.2).mpr hprime⟩

theorem prime_count_five_terms (left x : ℝ) (a b : ℕ) (z : ℕ → ℕ)
    (hleft : 1 ≤ left) (hlex : left ≤ x)
    (hsqrt : Nat.sqrt ⌊x⌋₊ ≤ ⌊left⌋₊)
    (hab : a ≤ b) (hbc : b ≤ topCutoff x)
    (hz : ∀ p ∈ primeBand a (topCutoff x), z p ≤ p) :
    ((primeWindow left x).card : ℝ) =
      siftedSum (window left x) a (fun _ => (1 : ℝ)) -
      (∑ p ∈ primeBand a b,
        siftedSum (divisorSlice (window left x) p) (z p) (fun _ => (1 : ℝ))) -
      (∑ p ∈ primeBand b (topCutoff x),
        siftedSum (divisorSlice (window left x) p) (z p) (fun _ => (1 : ℝ))) +
      (∑ p ∈ primeBand a b, ∑ q ∈ primeBand (z p) p,
        siftedSum (divisorSlice (window left x) (p * q)) q (fun _ => (1 : ℝ))) +
      ∑ p ∈ primeBand b (topCutoff x), ∑ q ∈ primeBand (z p) p,
        siftedSum (divisorSlice (window left x) (p * q)) q (fun _ => (1 : ℝ)) := by
  calc
    ((primeWindow left x).card : ℝ) =
        siftedSum (window left x) (topCutoff x) (fun _ => (1 : ℝ)) := by
      simp [siftedSum, sifted_top_eq_primeWindow left x hleft hlex hsqrt]
    _ = _ := weighted_buchstab_five_terms (window left x) a b (topCutoff x)
      z (fun _ => (1 : ℝ)) hab hbc hz

theorem prime_count_lower_without_second_correction (left x : ℝ)
    (a b : ℕ) (z : ℕ → ℕ)
    (hleft : 1 ≤ left) (hlex : left ≤ x)
    (hsqrt : Nat.sqrt ⌊x⌋₊ ≤ ⌊left⌋₊)
    (hab : a ≤ b) (hbc : b ≤ topCutoff x)
    (hz : ∀ p ∈ primeBand a (topCutoff x), z p ≤ p) :
    siftedSum (window left x) a (fun _ => (1 : ℝ)) -
      (∑ p ∈ primeBand a b,
        siftedSum (divisorSlice (window left x) p) (z p) (fun _ => (1 : ℝ))) -
      (∑ p ∈ primeBand b (topCutoff x),
        siftedSum (divisorSlice (window left x) p) (z p) (fun _ => (1 : ℝ))) +
      (∑ p ∈ primeBand a b, ∑ q ∈ primeBand (z p) p,
        siftedSum (divisorSlice (window left x) (p * q)) q (fun _ => (1 : ℝ))) ≤
      ((primeWindow left x).card : ℝ) := by
  have hpositive : 0 ≤
      (∑ p ∈ primeBand b (topCutoff x), ∑ q ∈ primeBand (z p) p,
        siftedSum (divisorSlice (window left x) (p * q)) q
          (fun _ => (1 : ℝ))) := by
    apply Finset.sum_nonneg
    intro p hp
    apply Finset.sum_nonneg
    intro q hq
    simp [siftedSum]
  rw [prime_count_five_terms left x a b z hleft hlex hsqrt hab hbc hz]
  exact le_add_of_nonneg_right hpositive

theorem divisorSlice_card_eq_divisorCount (left x : ℝ) (d : ℕ)
    (_hleft : 0 ≤ left) (hlex : left ≤ x) (_hd : 0 < d) :
    ((divisorSlice (window left x) d).card : ℝ) =
      HarmanDivisorWindow.divisorCount {d} (fun _ => 1) left x := by
  have hfloor : ⌊left⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hlex
  have hsubset :
      (Finset.Ioc 0 ⌊left⌋₊).filter (d ∣ ·) ⊆
        (Finset.Ioc 0 ⌊x⌋₊).filter (d ∣ ·) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans hfloor⟩, hn.2⟩
  have hslice :
      (divisorSlice (window left x) d) =
        ((Finset.Ioc 0 ⌊x⌋₊).filter (d ∣ ·)) \
          ((Finset.Ioc 0 ⌊left⌋₊).filter (d ∣ ·)) := by
    ext n
    simp only [divisorSlice, window, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_Ioc]
    omega
  rw [hslice, Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr hsubset]
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]
  have hdiv : ⌊left⌋₊ / d ≤ ⌊x⌋₊ / d := Nat.div_le_div_right hfloor
  rw [Nat.cast_sub hdiv]
  simp only [HarmanDivisorWindow.divisorCount, Finset.sum_singleton, one_mul]
  rw [Nat.floor_div_natCast, Nat.floor_div_natCast]

theorem prime_count_lower_frozen_cutoffs (left x : ℝ)
    (a b cLower cUpper : ℕ) (z : ℕ → ℕ)
    (hleft : 1 ≤ left) (hlex : left ≤ x)
    (hsqrt : Nat.sqrt ⌊x⌋₊ ≤ ⌊left⌋₊)
    (hab : a ≤ b) (hbl : b ≤ cLower)
    (hlc : cLower ≤ topCutoff x)
    (hcu : topCutoff x ≤ cUpper)
    (hz : ∀ p ∈ primeBand a (topCutoff x), z p ≤ p) :
    siftedSum (window left x) a (fun _ => (1 : ℝ)) -
      (∑ p ∈ primeBand a b,
        siftedSum (divisorSlice (window left x) p) (z p) (fun _ => (1 : ℝ))) -
      (∑ p ∈ primeBand b cUpper,
        siftedSum (divisorSlice (window left x) p) (z p) (fun _ => (1 : ℝ))) +
      (∑ p ∈ primeBand b cLower, ∑ q ∈ primeBand (z p) p,
        siftedSum (divisorSlice (window left x) (p * q)) q (fun _ => (1 : ℝ))) ≤
      ((primeWindow left x).card : ℝ) := by
  have hbc : b ≤ topCutoff x := hbl.trans hlc
  have hneg :
      (∑ p ∈ primeBand b (topCutoff x),
        siftedSum (divisorSlice (window left x) p) (z p) (fun _ => (1 : ℝ))) ≤
      (∑ p ∈ primeBand b cUpper,
        siftedSum (divisorSlice (window left x) p) (z p) (fun _ => (1 : ℝ))) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [primeBand, Finset.mem_filter, Finset.mem_Ico] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.trans_le hcu⟩, hp.2⟩
    · intro p hp _
      simp [siftedSum]
  have hpos :
      (∑ p ∈ primeBand b cLower, ∑ q ∈ primeBand (z p) p,
        siftedSum (divisorSlice (window left x) (p * q)) q (fun _ => (1 : ℝ))) ≤
      (∑ p ∈ primeBand b (topCutoff x), ∑ q ∈ primeBand (z p) p,
        siftedSum (divisorSlice (window left x) (p * q)) q (fun _ => (1 : ℝ))) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [primeBand, Finset.mem_filter, Finset.mem_Ico] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.trans_le hlc⟩, hp.2⟩
    · intro p hp _
      apply Finset.sum_nonneg
      intro q hq
      simp [siftedSum]
  have hfirst : 0 ≤
      (∑ p ∈ primeBand a b, ∑ q ∈ primeBand (z p) p,
        siftedSum (divisorSlice (window left x) (p * q)) q (fun _ => (1 : ℝ))) := by
    apply Finset.sum_nonneg
    intro p hp
    apply Finset.sum_nonneg
    intro q hq
    simp [siftedSum]
  rw [prime_count_five_terms left x a b z hleft hlex hsqrt hab hbc hz]
  linarith

end FiniteSieveWindow

run_cmd do
  for target in [``FiniteSieveWindow.rough_iff_prime,
      ``FiniteSieveWindow.sifted_top_eq_primeWindow,
      ``FiniteSieveWindow.prime_count_five_terms,
      ``FiniteSieveWindow.prime_count_lower_without_second_correction,
      ``FiniteSieveWindow.divisorSlice_card_eq_divisorCount,
      ``FiniteSieveWindow.prime_count_lower_frozen_cutoffs] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FINITE SIEVE WINDOW PASSED"
