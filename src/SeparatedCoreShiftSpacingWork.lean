import SeparatedCoreSharedPrimeWork

/-! Large source moduli force uniqueness at each nonzero short shift.
This is a spacing result, not an estimate for the centered correlation. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace SeparatedCoreShiftSpacingWork
open LongerTupleEncoding LongPairCloseDistinctMeanWork LongPairSeparatedCoreWork
open SeparatedCoreSharedPrimeWork PositiveSharpPowerWindow

theorem lcm_large_of_nearby (a b n m : ℕ) (B H : ℝ)
    (hB : 0≤B) (hH : 0<H) (hab : B*H<(a:ℝ)*b)
    (han : a∣n) (hbm : b∣m) (hne : n≠m) (hgap : |(n:ℝ)-m|<H) :
    B<(Nat.lcm a b:ℝ) := by
  have hg := common_divisor_gap (Nat.gcd a b) n m
    ((Nat.gcd_dvd_left a b).trans han) ((Nat.gcd_dvd_right a b).trans hbm) hne
  have hid : (Nat.gcd a b:ℝ)*(Nat.lcm a b:ℝ)=(a:ℝ)*b := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  by_contra hh
  have hl : (Nat.lcm a b:ℝ)≤B := le_of_not_gt hh
  have hp := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (Nat.gcd a b): (0:ℝ)≤_)
  have hq := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_le_of_lt hg hgap)) hB
  nlinarith

/-- Two pairs with the same oriented shift lie in one lcm progression. -/
theorem equal_shift_unique (a b n m n' m' : ℕ) (B : ℝ)
    (hl : B<(Nat.lcm a b:ℝ)) (hnB : (n:ℝ)≤B) (hnB' : (n':ℝ)≤B)
    (han : a∣n) (hbm : b∣m) (han' : a∣n') (hbm' : b∣m')
    (hshift : (n:ℤ)-m=(n':ℤ)-m') : n=n' ∧ m=m' := by
  have he : n+m'=n'+m := by omega
  have hne : n=n' := by
    by_contra hh
    rcases lt_or_gt_of_ne hh with hlt | hgt
    · have hs : n'-n=m'-m := by omega
      have hd : Nat.lcm a b∣n'-n := Nat.lcm_dvd
        (Nat.dvd_sub han' han) (by rw [hs]; exact Nat.dvd_sub hbm' hbm)
      have hc := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hd
      have hc' : (Nat.lcm a b:ℝ)≤(n':ℝ) := by exact_mod_cast hc.trans (Nat.sub_le _ _)
      linarith
    · have hs : n-n'=m-m' := by omega
      have hd : Nat.lcm a b∣n-n' := Nat.lcm_dvd
        (Nat.dvd_sub han han') (by rw [hs]; exact Nat.dvd_sub hbm hbm')
      have hc := Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) hd
      have hc' : (Nat.lcm a b:ℝ)≤(n:ℝ) := by exact_mod_cast hc.trans (Nat.sub_le _ _)
      linarith
  exact ⟨hne,by omega⟩

theorem eventually_source_spacing (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ r∈separatedSource X s, ∀ r'∈separatedSource X s,
      ∀ n m : ℕ, index r∣n → index r'∣m → n≠m →
        |(n:ℝ)-m|<2*halfWidth X (101/1000) →
        2*X<(Nat.lcm (index r) (index r'):ℝ) := by
  have hp := (tendsto_rpow_atTop
    (by norm_num : (0:ℝ)<52/35-1101/1000)).eventually (eventually_gt_atTop (2:ℝ))
  filter_upwards [hp,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000:ℝ))] with X hp hX hlog
  refine ⟨hX,hlog,?_⟩
  intro r hr r' hr' n m hn hm hne hgap
  have hXp : 0<X := by linarith
  have ha := (support_geometry X s hX hs hs1 hlog (index r)
    (Finset.mem_image.mpr ⟨r,hr,rfl⟩)).1
  have hb := (support_geometry X s hX hs hs1 hlog (index r')
    (Finset.mem_image.mpr ⟨r',hr',rfl⟩)).1
  have hp' := mul_lt_mul_of_pos_right hp (Real.rpow_pos_of_pos hXp (1101/1000:ℝ))
  rw [← Real.rpow_add hXp] at hp'
  norm_num at hp'
  have hprod : X^(52/35:ℝ)<(index r:ℝ)*(index r':ℝ) := by
    have hh := mul_lt_mul ha hb.le (Real.rpow_pos_of_pos hXp (26/35:ℝ))
      (Nat.cast_nonneg (index r) : (0:ℝ)≤(index r:ℝ))
    rw [← Real.rpow_add hXp] at hh
    norm_num at hh
    exact hh
  apply lcm_large_of_nearby (index r) (index r') n m (2*X)
    (2*halfWidth X (101/1000)) (by positivity) (by unfold halfWidth; positivity)
    _ hn hm hne hgap
  have hid : (2*X)*(2*halfWidth X (101/1000))=2*X^(1101/1000:ℝ) := by
    unfold halfWidth
    rw [show (1101/1000:ℝ)=1+101/1000 by norm_num, Real.rpow_add hXp, Real.rpow_one]
    ring
  rw [hid]
  exact hp'.trans hprod

run_cmd do
  for decl in [``lcm_large_of_nearby, ``equal_shift_unique, ``eventually_source_spacing] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SeparatedCoreShiftSpacingWork
