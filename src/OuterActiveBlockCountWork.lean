import OuterActiveDyadicWork

/-! The selected rectangular block family has only logarithmically many
labels; its size is independent of the separator frequency. -/
set_option autoImplicit false
noncomputable section
namespace OuterActiveBlockCountWork
open OuterActiveDyadicWork OuterSmoothSupportGeometryWork OuterSmoothErrorSupportWork
open OuterRampLengthWork OuterSourceReindexWork

def keyCarrier (X : ℝ) : Finset BlockKey :=
  Finset.range (⌊X⌋₊.log2+1) ×ˢ (Finset.range (⌊X⌋₊.log2+1) ×ˢ
    (Finset.range (⌊X⌋₊.log2+1) ×ˢ Finset.range (⌊X⌋₊.log2+1)))

theorem activeKeys_subset (X s : ℝ) (hX : 2 ≤ X) (i j : ℕ) :
    activeKeys X s i j ⊆ keyCarrier X := by
  intro k hk
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hk
  have hd := ambient_data X hX r (active_data X s i j r hr).1
  have hb := candidate_factor_bounds X (by linarith) (drop r) hd.2.1
  have hl (n : ℕ) (hn : (n:ℝ) ≤ X) : n.log2 < ⌊X⌋₊.log2+1 := by
    have hh := Nat.log_mono_right (b := 2) (Nat.le_floor hn)
    rw [← Nat.log2_eq_log_two,← Nat.log2_eq_log_two] at hh
    omega
  simp only [keyCarrier,blockKey,Finset.mem_product,Finset.mem_range]
  exact ⟨hl _ hd.2.2.2.1,hl _ hb.1,hl _ hb.2.1,hl _ hb.2.2⟩

theorem activeKeys_card (X s : ℝ) (hX : 2 ≤ X) (i j : ℕ) :
    (activeKeys X s i j).card ≤ (⌊X⌋₊.log2+1)^4 := by
  have hh := Finset.card_le_card (activeKeys_subset X s hX i j)
  simpa only [keyCarrier,Finset.card_product,Finset.card_range,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hh

theorem logarithmic_label_bound (X : ℝ) (hX : 2 ≤ X) :
    (⌊X⌋₊.log2:ℝ)+1 ≤ Real.log X/Real.log 2+1 := by
  have hn : 0 < ⌊X⌋₊ := by
    have hh : (1:ℕ) ≤ ⌊X⌋₊ := Nat.le_floor (by norm_num; linarith)
    omega
  have hp := Nat.log2_self_le (Nat.ne_of_gt hn)
  have hpX : (2:ℝ)^⌊X⌋₊.log2 ≤ X :=
    (by exact_mod_cast hp : (2:ℝ)^⌊X⌋₊.log2 ≤ ⌊X⌋₊).trans (Nat.floor_le (by linarith))
  have hl := Real.log_le_log (by positivity) hpX
  rw [Real.log_pow] at hl
  have hh := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hl
  linarith

theorem activeKeys_card_log (X s : ℝ) (hX : 2 ≤ X) (i j : ℕ) :
    ((activeKeys X s i j).card:ℝ) ≤ (Real.log X/Real.log 2+1)^4 := by
  calc
    _ ≤ ((⌊X⌋₊.log2:ℝ)+1)^4 := by exact_mod_cast activeKeys_card X s hX i j
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (logarithmic_label_bound X hX) 4

run_cmd do
  for decl in [``activeKeys_subset, ``activeKeys_card, ``logarithmic_label_bound,
      ``activeKeys_card_log] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterActiveBlockCountWork
