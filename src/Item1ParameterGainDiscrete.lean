import Item1ParameterGainBasic

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace Item1ParameterGain
open Item1ParameterCore

theorem selected_gain_le_total (a : ℝ) (d : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Icc 1 d) :
    (∑ j ∈ s, gain a (j:ℝ)) ≤ totalGain d a := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun j _ _ => gain_nonneg a j)

theorem totalGain_small_left (a : ℝ) (ha : 1 ≤ a) (hb : a ≤ 4/3) :
    a^2/3 ≤ totalGain (degree a) a := by
  have hd := degree_ge_five a ha
  have hsub : ({2,3}:Finset ℕ) ⊆ Finset.Icc 1 (degree a) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
  have hs := selected_gain_le_total a (degree a) {2,3} hsub
  have h₂ : a-2/3 ≤ gain a 2 := by apply le_gain <;> linarith
  have h₃ : a-1 ≤ gain a 3 := by apply le_gain <;> linarith
  norm_num at hs
  have hquad := mul_nonneg (sub_nonneg.mpr ha) (by linarith : 0 ≤ 5-a)
  nlinarith

theorem totalGain_small_right (a : ℝ) (ha : 4/3 ≤ a) (hb : a ≤ 2) :
    a^2/3 ≤ totalGain (degree a) a := by
  have hd := degree_ge_five a (by linarith)
  have hsub : ({2,3,4}:Finset ℕ) ⊆ Finset.Icc 1 (degree a) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
  have hs := selected_gain_le_total a (degree a) {2,3,4} hsub
  have h₂ : 2-a ≤ gain a 2 := by apply le_gain <;> linarith
  have h₃ : a-1 ≤ gain a 3 := by apply le_gain <;> linarith
  have h₄ : a-4/3 ≤ gain a 4 := by apply le_gain <;> linarith
  norm_num at hs
  have hquad := mul_nonneg (by linarith : 0 ≤ a) (by linarith : 0 ≤ 2-a)
  nlinarith

theorem totalGain_small (a : ℝ) (ha : 1 ≤ a) (hb : a ≤ 2) :
    a^2/3 ≤ totalGain (degree a) a := by
  rcases le_total a (4/3) with h | h
  · exact totalGain_small_left a ha h
  · exact totalGain_small_right a h hb

theorem floor_ge_two_thirds (a : ℝ) (ha : 2 ≤ a) :
    2*a/3 ≤ (Nat.floor a:ℝ) := by
  have hf : 2 ≤ Nat.floor a := Nat.le_floor (by exact_mod_cast ha)
  have hf' : (2:ℝ) ≤ Nat.floor a := by exact_mod_cast hf
  have hlt := Nat.lt_floor_add_one a
  linarith

theorem totalGain_large (a : ℝ) (ha : 2 ≤ a) :
    a^2/6 ≤ totalGain (degree a) a := by
  let q : ℕ := Nat.ceil (5*a/4)
  let n : ℕ := Nat.floor a
  have hqlo : 5*a/4 ≤ (q:ℝ) := Nat.le_ceil _
  have hqhi : (q:ℝ) < 5*a/4+1 := Nat.ceil_lt_add_one (by linarith)
  have hnhi : (n:ℝ) ≤ a := Nat.floor_le (by linarith)
  have hdlo : 3*a+2 ≤ (degree a:ℝ) := by
    have hc := Nat.le_ceil (3*a)
    simp only [degree, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hpoint (k : ℕ) (hk : k ∈ Finset.range n) :
      5*a/4 ≤ ((q+k:ℕ):ℝ) ∧ ((q+k:ℕ):ℝ) ≤ 9*a/4 := by
    have hkn : k+1 ≤ n := by have := Finset.mem_range.mp hk; omega
    have hkn' : (k:ℝ)+1 ≤ n := by exact_mod_cast hkn
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    push_cast
    constructor <;> linarith
  have hsub : (Finset.range n).image (fun k => q+k) ⊆ Finset.Icc 1 (degree a) := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨k,hk,rfl⟩
    have hh := hpoint k hk
    have hlo : (1:ℝ) ≤ ((q+k:ℕ):ℝ) := by linarith
    have hhi : ((q+k:ℕ):ℝ) ≤ (degree a:ℝ) := by linarith
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hs := selected_gain_le_total a (degree a)
    ((Finset.range n).image (fun k => q+k)) hsub
  rw [Finset.sum_image (by intro i hi j hj hij; exact Nat.add_left_cancel hij)] at hs
  have hlower : (n:ℝ)*(a/4) ≤ ∑ k ∈ Finset.range n, gain a ((q+k:ℕ):ℝ) := by
    calc
      (n:ℝ)*(a/4) = ∑ _k ∈ Finset.range n, a/4 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun k hk =>
        gain_on_middle a ((q+k:ℕ):ℝ) (hpoint k hk).1 (hpoint k hk).2)
  have hnlo : 2*a/3 ≤ (n:ℝ) := floor_ge_two_thirds a ha
  have hprod := mul_le_mul_of_nonneg_right hnlo (by linarith : 0 ≤ a/4)
  nlinarith [hlower.trans hs]

end Item1ParameterGain

run_cmd do
  for target in [``Item1ParameterGain.selected_gain_le_total,
      ``Item1ParameterGain.totalGain_small_left, ``Item1ParameterGain.totalGain_small_right,
      ``Item1ParameterGain.totalGain_small, ``Item1ParameterGain.floor_ge_two_thirds,
      ``Item1ParameterGain.totalGain_large] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER GAIN DISCRETE: 6 standard-axiom theorem guards passed."
