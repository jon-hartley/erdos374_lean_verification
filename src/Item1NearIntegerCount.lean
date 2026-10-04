import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! Elementary counting of integer multiples close to integers.
The estimate is Ford's (5.6) with a natural radius, including radius zero.
No rational approximation or polynomial mean-value bound is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators Classical

namespace Item1NearIntegerCount

/-- A finite integer set in a real interval has at most length plus one points. -/
theorem card_le_real_interval_length (s : Finset ℤ) (a b : ℝ) (hab : a ≤ b)
    (hs : ∀ n ∈ s, a ≤ (n:ℝ) ∧ (n:ℝ) ≤ b) :
    (s.card:ℝ) ≤ b-a+1 := by
  by_cases hn : s.Nonempty
  · have hlo := (hs (s.min' hn) (s.min'_mem hn)).1
    have hhi := (hs (s.max' hn) (s.max'_mem hn)).2
    have hle := s.min'_le_max' hn
    have hsub : s ⊆ Finset.Icc (s.min' hn) (s.max' hn) := by
      intro n hn'
      exact Finset.mem_Icc.mpr ⟨s.min'_le n hn', s.le_max' n hn'⟩
    have hc : (s.card:ℝ) ≤ ((Finset.Icc (s.min' hn) (s.max' hn)).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hcard : ((Finset.Icc (s.min' hn) (s.max' hn)).card:ℝ) =
        (s.max' hn:ℝ)+1-(s.min' hn:ℝ) := by
      exact_mod_cast Int.card_Icc_of_le (s.min' hn) (s.max' hn)
        (show s.min' hn ≤ s.max' hn + 1 by omega)
    rw [hcard] at hc
    linarith
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.card_empty, Nat.cast_zero]
    linarith

/-- A fixed target integer receives at most 2*delta/gamma+1 multiples. -/
theorem card_mul_close (s : Finset ℤ) (γ δ m : ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hs : ∀ d ∈ s, |(d:ℝ)*γ-m| < δ) :
    (s.card:ℝ) ≤ 2*δ/γ+1 := by
  have hh := card_le_real_interval_length s ((m-δ)/γ) ((m+δ)/γ)
    (div_le_div_of_nonneg_right (by linarith) hγ.le) (by
      intro d hd
      have h := abs_lt.mp (hs d hd)
      constructor
      · exact (div_le_iff₀ hγ).mpr (by linarith)
      · exact (le_div_iff₀ hγ).mpr (by linarith))
  convert hh using 1
  ring

/-- The finite set counted by the near-integer estimate. -/
def nearIntegerSet (K : ℕ) (γ δ : ℝ) : Finset ℤ :=
  (Finset.Icc (-(K:ℤ)) (K:ℤ)).filter
    (fun d => |(d:ℝ)*γ-(round ((d:ℝ)*γ):ℝ)| < δ)

/-- For delta below 1/2, group the multiples by their nearest integer. -/
theorem near_integer_count_small (K : ℕ) (γ δ : ℝ)
    (hγ : 0 < γ) (hδ : 0 < δ) (hhalf : δ < 1/2) :
    ((nearIntegerSet K γ δ).card:ℝ) ≤
      4*(K:ℝ)*δ+2*(K:ℝ)*γ+4*δ/γ+2 := by
  let S := nearIntegerSet K γ δ
  let f : ℤ → ℤ := fun d => round ((d:ℝ)*γ)
  have hK : 0 ≤ (K:ℝ) := Nat.cast_nonneg K
  have hbox (d : ℤ) (hd : d ∈ S) : -(K:ℝ) ≤ (d:ℝ) ∧ (d:ℝ) ≤ K := by
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    exact_mod_cast h
  have hnear (d : ℤ) (hd : d ∈ S) : |(d:ℝ)*γ-(f d:ℝ)| < δ :=
    (Finset.mem_filter.mp hd).2
  have hfiber (m : ℤ) : ((S.filter (fun d => f d = m)).card:ℝ) ≤ 2*δ/γ+1 := by
    apply card_mul_close _ γ δ (m:ℝ) hγ hδ
    intro d hd
    have hh := Finset.mem_filter.mp hd
    simpa only [hh.2] using hnear d hh.1
  have himage : ((S.image f).card:ℝ) ≤ 2*(K:ℝ)*γ+2 := by
    have hh := card_le_real_interval_length (S.image f)
      (-(K:ℝ)*γ-δ) ((K:ℝ)*γ+δ) (by nlinarith) (by
        intro m hm
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
        have hb := hbox d hd
        have hn := abs_lt.mp (hnear d hd)
        have hl := mul_le_mul_of_nonneg_right hb.1 hγ.le
        have hu := mul_le_mul_of_nonneg_right hb.2 hγ.le
        constructor <;> linarith)
    linarith
  have hcard : (S.card:ℝ) =
      ∑ m ∈ S.image f, ((S.filter (fun d => f d = m)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image f S
  change (S.card:ℝ) ≤ _
  rw [hcard]
  calc
    _ ≤ ∑ _m ∈ S.image f, (2*δ/γ+1) :=
      Finset.sum_le_sum (fun m _ => hfiber m)
    _ = ((S.image f).card:ℝ)*(2*δ/γ+1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2*(K:ℝ)*γ+2)*(2*δ/γ+1) :=
      mul_le_mul_of_nonneg_right himage (by positivity)
    _ = _ := by field_simp; ring

/-- Ford's elementary near-integer count, with no restriction on delta. -/
theorem near_integer_count (K : ℕ) (γ δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ) :
    ((nearIntegerSet K γ δ).card:ℝ) ≤
      4*(K:ℝ)*δ+2*(K:ℝ)*γ+4*δ/γ+2 := by
  by_cases hhalf : δ < 1/2
  · exact near_integer_count_small K γ δ hγ hδ hhalf
  · have hδhalf : 1/2 ≤ δ := le_of_not_gt hhalf
    have hK : 0 ≤ (K:ℝ) := Nat.cast_nonneg K
    have hc := card_le_real_interval_length (nearIntegerSet K γ δ)
      (-(K:ℝ)) (K:ℝ) (by linarith) (by
        intro d hd
        have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
        exact_mod_cast h)
    have hkg : 0 ≤ (K:ℝ)*γ := mul_nonneg hK hγ.le
    have hdg : 0 ≤ 4*δ/γ := by positivity
    have hkd : 2*(K:ℝ) ≤ 4*(K:ℝ)*δ := by nlinarith
    linarith

end Item1NearIntegerCount

run_cmd do
  for target in [``Item1NearIntegerCount.card_le_real_interval_length,
      ``Item1NearIntegerCount.card_mul_close,
      ``Item1NearIntegerCount.near_integer_count_small,
      ``Item1NearIntegerCount.near_integer_count] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "NEAR INTEGER COUNT: 4 standard-axiom theorem guards passed."
