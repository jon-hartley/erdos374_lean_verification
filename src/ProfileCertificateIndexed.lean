import ProfileCertificatePadded

set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

noncomputable section
namespace ProfileCertificateIndexed

open ProfileCertificateArithmetic

def profiles : List (List ℕ) := [ProfileCertificatePadded.profile0, ProfileCertificatePadded.profile1, ProfileCertificatePadded.profile2, ProfileCertificatePadded.profile3, ProfileCertificatePadded.profile4, ProfileCertificatePadded.profile5, ProfileCertificatePadded.profile6, ProfileCertificatePadded.profile7, ProfileCertificatePadded.profile8, ProfileCertificatePadded.profile9, ProfileCertificatePadded.profile10]

def entry (n j : ℕ) : ℕ := (profiles[n]!)[j]!

def matrixEntry (i j : ℕ) : ℕ := (ProfileCertificateTables.matrix[i]!)[j]!

def forceEntry (i : ℕ) : ℕ := ProfileCertificateTables.forces[i]!

def value (n j : ℕ) : ℝ := (entry n j : ℝ)/1000000000

def coefficient (n j : ℕ) : ℝ := value n j-value n (j+1)

def matrixValue (i j : ℕ) : ℝ := (matrixEntry i j : ℝ)/1000000000

def forceValue (i : ℕ) : ℝ := (forceEntry i : ℝ)/1000000000

theorem entries_decrease : ∀ n : Fin 11, ∀ j : Fin 90, entry n.val (j.val+1) ≤ entry n.val j.val := by decide

theorem entries_terminal : ∀ n : Fin 11, entry n.val 90 = 0 := by decide

theorem seeds_checked : ∀ j : Fin 90, scale*4095*5^j.val ≤ entry 0 j.val*331*6^j.val := by decide

theorem step0_indexed : ∀ i : Fin 90,
    scale*forceEntry i.val + scale*100000 + scale*10000 +
      ∑ j ∈ Finset.range 90, matrixEntry i.val j*(entry 0 j-entry 0 (j+1))
      ≤ scale*entry 1 i.val := by decide

theorem step1_indexed : ∀ i : Fin 90,
    scale*forceEntry i.val + scale*100000 + scale*10000 +
      ∑ j ∈ Finset.range 90, matrixEntry i.val j*(entry 1 j-entry 1 (j+1))
      ≤ scale*entry 2 i.val := by decide

theorem step2_indexed : ∀ i : Fin 90,
    scale*forceEntry i.val + scale*100000 + scale*10000 +
      ∑ j ∈ Finset.range 90, matrixEntry i.val j*(entry 2 j-entry 2 (j+1))
      ≤ scale*entry 3 i.val := by decide

theorem step3_indexed : ∀ i : Fin 90,
    scale*forceEntry i.val + scale*100000 + scale*10000 +
      ∑ j ∈ Finset.range 90, matrixEntry i.val j*(entry 3 j-entry 3 (j+1))
      ≤ scale*entry 4 i.val := by decide

theorem step4_indexed : ∀ i : Fin 90,
    scale*forceEntry i.val + scale*100000 + scale*10000 +
      ∑ j ∈ Finset.range 90, matrixEntry i.val j*(entry 4 j-entry 4 (j+1))
      ≤ scale*entry 5 i.val := by decide

theorem step5_indexed : ∀ i : Fin 90,
    scale*forceEntry i.val + scale*100000 + scale*10000 +
      ∑ j ∈ Finset.range 90, matrixEntry i.val j*(entry 5 j-entry 5 (j+1))
      ≤ scale*entry 6 i.val := by decide

theorem step6_indexed : ∀ i : Fin 90,
    scale*forceEntry i.val + scale*100000 + scale*10000 +
      ∑ j ∈ Finset.range 90, matrixEntry i.val j*(entry 6 j-entry 6 (j+1))
      ≤ scale*entry 7 i.val := by decide

theorem step7_indexed : ∀ i : Fin 90,
    scale*forceEntry i.val + scale*100000 + scale*10000 +
      ∑ j ∈ Finset.range 90, matrixEntry i.val j*(entry 7 j-entry 7 (j+1))
      ≤ scale*entry 8 i.val := by decide

theorem step8_indexed : ∀ i : Fin 90,
    scale*forceEntry i.val + scale*100000 + scale*10000 +
      ∑ j ∈ Finset.range 90, matrixEntry i.val j*(entry 8 j-entry 8 (j+1))
      ≤ scale*entry 9 i.val := by decide

theorem step9_indexed : ∀ i : Fin 90,
    scale*forceEntry i.val + scale*100000 + scale*10000 +
      ∑ j ∈ Finset.range 90, matrixEntry i.val j*(entry 9 j-entry 9 (j+1))
      ≤ scale*entry 10 i.val := by decide

theorem steps_indexed (n : Fin 10) (i : Fin 90) :
    scale*forceEntry i.val + scale*100000 + scale*10000 +
      ∑ j ∈ Finset.range 90, matrixEntry i.val j*(entry n.val j-entry n.val (j+1))
      ≤ scale*entry (n.val+1) i.val := by
  fin_cases n
  · exact step0_indexed i
  · exact step1_indexed i
  · exact step2_indexed i
  · exact step3_indexed i
  · exact step4_indexed i
  · exact step5_indexed i
  · exact step6_indexed i
  · exact step7_indexed i
  · exact step8_indexed i
  · exact step9_indexed i


theorem coefficient_nonneg (n : Fin 11) (j : Fin 90) : 0 ≤ coefficient n.val j.val := by
  unfold coefficient value
  exact sub_nonneg.mpr (div_le_div_of_nonneg_right
    (by exact_mod_cast entries_decrease n j) (by norm_num))

theorem value_terminal (n : Fin 11) : value n.val 90 = 0 := by
  simp only [value, entries_terminal n, Nat.cast_zero, zero_div]

theorem real_step (n : Fin 10) (i : Fin 90) :
    forceValue i.val + 1/10000 + 1/100000 +
      ∑ j ∈ Finset.range 90, matrixValue i.val j * coefficient n.val j
      ≤ value (n.val+1) i.val := by
  have hn : n.val < 11 := by omega
  have hs : (((∑ j ∈ Finset.range 90,
      matrixEntry i.val j*(entry n.val j-entry n.val (j+1))) : ℕ) : ℝ) =
      ∑ j ∈ Finset.range 90, (matrixEntry i.val j : ℝ)*
        ((entry n.val j : ℝ)-(entry n.val (j+1) : ℝ)) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.cast_mul, Nat.cast_sub (entries_decrease ⟨n.val, hn⟩ ⟨j, Finset.mem_range.mp hj⟩)]
  have h : (1000000000 : ℝ)*forceEntry i.val + 1000000000*100000 +
      1000000000*10000 +
      ∑ j ∈ Finset.range 90, (matrixEntry i.val j : ℝ)*
        ((entry n.val j : ℝ)-(entry n.val (j+1) : ℝ))
      ≤ 1000000000*(entry (n.val+1) i.val : ℝ) := by
    have hcast := (show (((scale*forceEntry i.val+scale*100000+scale*10000+
      ∑ j ∈ Finset.range 90, matrixEntry i.val j*(entry n.val j-entry n.val (j+1))) : ℕ) : ℝ)
      ≤ ((scale*entry (n.val+1) i.val : ℕ) : ℝ) by exact_mod_cast steps_indexed n i)
    push_cast only [Nat.cast_add, Nat.cast_mul] at hcast
    rw [hs] at hcast
    simpa only [scale, Nat.cast_ofNat] using hcast
  have hd := div_le_div_of_nonneg_right h (show (0 : ℝ) ≤ 1000000000000000000 by norm_num)
  convert hd using 1
  · simp only [forceValue, matrixValue, coefficient, value]
    rw [add_div, add_div, add_div, Finset.sum_div]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  · simp only [value]
    ring

theorem initial_rational_bound (j : Fin 90) :
    (4095/331 : ℝ)*(5/6 : ℝ)^j.val ≤ value 0 j.val := by
  have h : (1000000000 : ℝ)*4095*5^j.val ≤
      (entry 0 j.val : ℝ)*331*6^j.val := by
    exact_mod_cast seeds_checked j
  unfold value
  have hid : (4095/331 : ℝ)*(5/6 : ℝ)^j.val =
      (4095*5^j.val)/(331*6^j.val) := by rw [div_pow]; ring
  rw [hid]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<331*6^j.val)
    (by norm_num : (0 : ℝ)<1000000000)).mpr
  convert h using 1 <;> ring

theorem final_value : value 10 10 = (53589103/1000000000 : ℝ) := by
  change (ProfileCertificatePadded.profile10[10]! : ℝ)/1000000000 = _
  rw [ProfileCertificatePadded.final_exact]
  norm_num

theorem final_lt : value 10 10 < (1/16 : ℝ) := by
  rw [final_value]
  norm_num

run_cmd do
  for decl in [``entries_decrease, ``entries_terminal, ``seeds_checked, ``step0_indexed, ``step1_indexed, ``step2_indexed, ``step3_indexed, ``step4_indexed, ``step5_indexed, ``step6_indexed, ``step7_indexed, ``step8_indexed, ``step9_indexed, ``steps_indexed, ``coefficient_nonneg, ``value_terminal, ``real_step, ``initial_rational_bound, ``final_value, ``final_lt] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "INDEXED REAL PROFILE BUDGETS: STANDARD AXIOMS ONLY"
end ProfileCertificateIndexed
end
