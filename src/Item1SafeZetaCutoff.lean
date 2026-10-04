import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Scalar geometry for the repaired Euler cutoff.
The cutoff is at t^2, not t. No zeta or phase estimate is used here. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Item1SafeZetaCutoff

def cutoffIndex (t : ℝ) : ℕ := Nat.ceil (2*Real.log t/Real.log 2)

theorem cutoff_bounds (t : ℝ) (ht : 1≤t) (hL : 1≤Real.log t) :
    t^2≤((2^(cutoffIndex t):ℕ):ℝ) ∧
    ((2^(cutoffIndex t):ℕ):ℝ)<2*t^2 ∧
    (cutoffIndex t:ℝ)≤5*Real.log t := by
  have htp : 0<t := by linarith
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h2lo : (1/2:ℝ)≤Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    linarith
  have hq : 0≤2*Real.log t/Real.log 2 := by positivity
  have hlo : 2*Real.log t/Real.log 2≤(cutoffIndex t:ℝ) := Nat.le_ceil _
  have hhi : (cutoffIndex t:ℝ)<2*Real.log t/Real.log 2+1 :=
    Nat.ceil_lt_add_one hq
  have hlo' : 2*Real.log t≤(cutoffIndex t:ℝ)*Real.log 2 :=
    (div_le_iff₀ h2).mp hlo
  have hhi' : (cutoffIndex t:ℝ)*Real.log 2<2*Real.log t+Real.log 2 := by
    have hh := mul_lt_mul_of_pos_right hhi h2
    field_simp at hh
    nlinarith
  have hQp : (0:ℝ)<(2:ℝ)^cutoffIndex t := by positivity
  have hQl : Real.log ((2:ℝ)^cutoffIndex t)=
      (cutoffIndex t:ℝ)*Real.log 2 := Real.log_pow _ _
  have hQlo : t^2≤(2:ℝ)^cutoffIndex t := by
    apply (Real.log_le_log_iff (by positivity) hQp).mp
    rw [hQl,Real.log_pow]
    norm_num
    exact hlo'
  have hQhi : (2:ℝ)^cutoffIndex t<2*t^2 := by
    apply (Real.log_lt_log_iff hQp (by positivity)).mp
    rw [hQl,Real.log_mul (by norm_num) (pow_ne_zero 2 htp.ne'),Real.log_pow]
    norm_num
    linarith
  have hfrac : 2*Real.log t/Real.log 2≤4*Real.log t := by
    apply (div_le_iff₀ h2).mpr
    nlinarith [mul_nonneg (by linarith : 0≤Real.log 2-1/2)
      (by linarith : 0≤Real.log t)]
  refine ⟨?_,?_,by linarith⟩
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hQlo
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hQhi

theorem block_below_square (t : ℝ) (ht : 1≤t) (hL : 1≤Real.log t)
    (j : ℕ) (hj : j<cutoffIndex t) : ((2^j:ℕ):ℝ)≤t^2 := by
  have hQ := (cutoff_bounds t ht hL).2.1
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
    (show j+1≤cutoffIndex t by omega)
  have hp' : 2*((2^j:ℕ):ℝ)≤((2^(cutoffIndex t):ℕ):ℝ) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,pow_succ,mul_comm] using hp
  linarith

theorem strip_sigma_lower (L sigma : ℝ) (hL : 8≤L)
    (hs : 1-1/L^(2/3:ℝ)≤sigma) : 3/4≤sigma := by
  have h8 : (8:ℝ)^(2/3:ℝ)=4 := by
    calc
      _ = ((2:ℝ)^3)^(2/3:ℝ) := by norm_num
      _ = (2:ℝ)^((3:ℝ)*(2/3)) := (Real.rpow_natCast_mul (by norm_num) 3 (2/3)).symm
      _ = 4 := by norm_num
  have hh : 4≤L^(2/3:ℝ) := by
    have hh := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤8) hL (by norm_num : (0:ℝ)≤2/3)
    simpa only [h8] using hh
  have hp : 0<L^(2/3:ℝ) := by linarith
  have hi : 1/L^(2/3:ℝ)≤1/4 := (div_le_iff₀ hp).mpr (by linarith)
  linarith

/-- The exact powers in the Euler bound are small with the enlarged cutoff. -/
theorem cutoff_powers (Q : ℕ) (t sigma : ℝ) (ht : 2≤t)
    (hQlo : t^2≤(Q:ℝ)) (hQhi : (Q:ℝ)<2*t^2)
    (hs : 3/4≤sigma) (hs1 : sigma≤1) :
    (Q:ℝ)^(1-sigma)≤t ∧ (Q:ℝ)^(-sigma)≤1/t := by
  have htp : 0<t := by linarith
  have hQp : (0:ℝ)<Q := lt_of_lt_of_le (sq_pos_of_pos htp) hQlo
  have hQ1 : (1:ℝ)≤Q := by nlinarith
  have hQt4 : (Q:ℝ)≤t^4 := by
    have hh : 2*t^2≤t^4 := by
      have hp := mul_nonneg (show 0≤t^2-2 by nlinarith) (sq_nonneg t)
      nlinarith
    exact hQhi.le.trans hh
  constructor
  · calc
      _ ≤ (Q:ℝ)^(1/4:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
      _ ≤ (t^4)^(1/4:ℝ) := Real.rpow_le_rpow hQp.le hQt4 (by norm_num)
      _ = t := by rw [←Real.rpow_natCast_mul htp.le 4 (1/4:ℝ)]; norm_num
  · calc
      _ ≤ (t^2)^(-sigma) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos htp) hQlo (by linarith)
      _ = t^((-2)*sigma) := by
        rw [←Real.rpow_natCast_mul htp.le 2 (-sigma)]
        congr 1
        ring
      _ ≤ t^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1/t := by rw [Real.rpow_neg_one, one_div]

end Item1SafeZetaCutoff

run_cmd do
  for n in [``Item1SafeZetaCutoff.cutoff_bounds,
    ``Item1SafeZetaCutoff.block_below_square,
    ``Item1SafeZetaCutoff.strip_sigma_lower,
    ``Item1SafeZetaCutoff.cutoff_powers] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
