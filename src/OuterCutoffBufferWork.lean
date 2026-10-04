import OuterSparseBoundaryWork

/-! Remove at most three integers near each real cutoff. Away from this
set, logarithmic distance from the cutoff has a uniform polynomial lower
bound for outer primes at most X. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable

namespace OuterCutoffBufferWork

def nearCutoff (v : ℝ) : Finset ℕ := Finset.Icc (⌊v⌋₊-1) (⌊v⌋₊+1)

theorem nearCutoff_card (v : ℝ) : (nearCutoff v).card≤3 := by
  simp only [nearCutoff,Nat.card_Icc]
  omega

theorem unit_gap_of_not_mem (v : ℝ) (hv : 0≤v) (p : ℕ)
    (hp : p∉nearCutoff v) : 1 < |(p:ℝ)-v| := by
  by_contra hn
  have hh := abs_le.mp (le_of_not_gt hn)
  have hlo := Nat.floor_le hv
  have hhi := Nat.lt_floor_add_one v
  have hpLo : ⌊v⌋₊ ≤ p+1 := by
    have hh' : (⌊v⌋₊:ℝ) ≤ ((p+1:ℕ):ℝ) := by push_cast; linarith
    exact_mod_cast hh'
  have hpHi : p < ⌊v⌋₊+2 := by
    have hh' : (p:ℝ) < ((⌊v⌋₊+2:ℕ):ℝ) := by push_cast; linarith
    exact_mod_cast hh'
  apply hp
  simp only [nearCutoff,Finset.mem_Icc]
  omega

theorem log_diff_lower (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    (y-x)/y ≤ Real.log y-Real.log x := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)] at hh
  have he : (y-x)/y = 1-x/y := by field_simp <;> ring
  rw [he]
  linarith

theorem log_gap_of_unit_gap (X p v : ℝ) (hp : 1≤p) (hpX : p≤X)
    (hv : 0<v) (hgap : 1 < |p-v|) :
    1/(2*X) ≤ |Real.log p-Real.log v| := by
  have hp0 : 0<p := by linarith
  have hX : 0<X := hp0.trans_le hpX
  by_cases hvp : v≤p
  · rw [abs_of_nonneg (sub_nonneg.mpr hvp)] at hgap
    have hlog := Real.log_le_log hv hvp
    rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
    calc
      _ ≤ 1/p := div_le_div_of_nonneg_left (by norm_num) hp0 (by linarith)
      _ ≤ (p-v)/p := div_le_div_of_nonneg_right hgap.le hp0.le
      _ ≤ _ := log_diff_lower v p hv hp0
  · have hpv : p<v := lt_of_not_ge hvp
    rw [abs_of_neg (sub_neg.mpr hpv)] at hgap
    have hp1v : p+1≤v := by linarith
    have hlog := Real.log_le_log hp0 hpv.le
    rw [abs_of_nonpos (sub_nonpos.mpr hlog)]
    calc
      _ ≤ 1/(p+1) := div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
      _ = ((p+1)-p)/(p+1) := by ring
      _ ≤ Real.log (p+1)-Real.log p := log_diff_lower p (p+1) hp0 (by linarith)
      _ ≤ -(Real.log p-Real.log v) := by
        have hh := Real.log_le_log (by linarith : 0<p+1) hp1v
        linarith

theorem log_gap_of_not_mem (X v : ℝ) (p : ℕ) (hp : 0<p) (hpX : (p:ℝ)≤X)
    (hv : 0<v) (hnot : p∉nearCutoff v) :
    1/(2*X) ≤ |Real.log (p:ℝ)-Real.log v| :=
  log_gap_of_unit_gap X p v (by exact_mod_cast hp) hpX hv
    (unit_gap_of_not_mem v hv.le p hnot)

run_cmd do
  for decl in [``nearCutoff_card, ``unit_gap_of_not_mem, ``log_diff_lower,
      ``log_gap_of_unit_gap, ``log_gap_of_not_mem] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterCutoffBufferWork
