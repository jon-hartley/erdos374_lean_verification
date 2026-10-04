import MomentThreshold
import MomentGrowthEnvelope

/-!
A logarithmic, not subpower, envelope for the inherited finite moment bound.
All premises here are explicit numerical bounds
on the coefficients of that finite bound, not a source residual mean.
The extra dyadic logarithm is deliberately retained: for h <= 5 the cost
is at most log^18, which still leaves the final power-30 raw mean unchanged.
-/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace SourceLogMomentEnvelope
open MomentThreshold SupremumMoment MomentLengthRatio

def cut (Q T p : ℝ) : ℝ := cutoff (T/Q^2) 1 p

theorem log_two_lower : (1/2 : ℝ) ≤ Real.log 2 := by
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)
  rw [Real.log_inv] at hh
  norm_num at hh
  linarith

theorem cutoff_log (Q T p : ℝ) (hQ : 0 < Q) (hT : 0 < T) :
    Real.log (cut Q T p) = (Real.log T-2*Real.log Q)/(6-p) := by
  unfold cut cutoff
  rw [div_one, Real.log_rpow (div_pos hT (sq_pos_of_pos hQ)),
    Real.log_div hT.ne' (pow_ne_zero 2 hQ.ne'), Real.log_pow]
  norm_num
  ring

/-- The amplitude-band count costs only one logarithm, uniformly in p. -/
theorem band_count (Q T p L : ℝ) (h : ℕ) (C : ℝ)
    (hQ : 1 ≤ Q) (hT : 1 ≤ T) (_hp : 2 ≤ p) (hp3 : p ≤ 3)
    (hL : 1 ≤ L) (hC : 1 ≤ C)
    (hqlog : Real.log Q ≤ (h:ℝ)*L) (hclog : Real.log C ≤ 6*(h:ℝ)) :
    bandCountBound (cut Q T p) C ≤ (1+14*(h:ℝ))*L := by
  have hQp : 0 < Q := by linarith
  have hTp : 0 < T := by linarith
  have hCp : 0 < C := by linarith
  have hLp : 0 ≤ L := by linarith
  have hd : 0 < 6-p := by linarith
  have hv : 0 < cut Q T p := cutoff_positive _ _ _ (by positivity) (by norm_num)
  have hq0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have ht0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hneg : -Real.log (cut Q T p) ≤ (2/3)*Real.log Q := by
    rw [cutoff_log Q T p hQp hTp]
    have he : -(Real.log T-2*Real.log Q)/(6-p) =
        (2*Real.log Q-Real.log T)/(6-p) := by ring
    rw [←neg_div, he]
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ 3-p by linarith) hq0]
  have hcL : Real.log C ≤ 6*(h:ℝ)*L := by
    have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ 6*(h:ℝ) by positivity)
    linarith
  have hratio : Real.log (C/cut Q T p) ≤ (20/3)*(h:ℝ)*L := by
    rw [Real.log_div hCp.ne' hv.ne']
    have hh := mul_le_mul_of_nonneg_left hqlog (by norm_num : (0:ℝ) ≤ 2/3)
    linarith
  have hmax : Real.log (max (C/cut Q T p) 1) ≤ (20/3)*(h:ℝ)*L := by
    rcases le_total (C/cut Q T p) 1 with hh | hh
    · rw [max_eq_right hh, Real.log_one]
      positivity
    · rw [max_eq_left hh]
      exact hratio
  have htwp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdv : Real.log (max (C/cut Q T p) 1)/Real.log 2 ≤ 14*(h:ℝ)*L := by
    apply (div_le_iff₀ htwp).mpr
    have hh := mul_le_mul_of_nonneg_left log_two_lower
      (show 0 ≤ 14*(h:ℝ)*L by positivity)
    nlinarith [mul_nonneg (Nat.cast_nonneg h : (0:ℝ) ≤ _) hLp]
  unfold bandCountBound
  nlinarith

/-- This is an algebraic simplification of the actual finite moment estimate.
Its only analytic role is to keep every loss logarithmic. -/
theorem envelope (Q T p L C A B M ca cb cm : ℝ) (h : ℕ)
    (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (hL : 1 ≤ L) (hC : 1 ≤ C)
    (hqlog : Real.log Q ≤ (h:ℝ)*L) (hclog : Real.log C ≤ 6*(h:ℝ))
    (hlen : T^4 ≤ Q^(p+2))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hM : 0 ≤ M)
    (hca : 0 ≤ ca) (hcb : 0 ≤ cb) (hcm : 0 ≤ cm)
    (ha : A ≤ ca*L^(h+1))
    (hb : B ≤ cb*(T/Q^2)*L^(3*h+2))
    (hm : M ≤ cm*L^(h+1)*(1+T/Q)) :
    (cut Q T p)^(p-2)*M+
      bandCountBound (cut Q T p) C*(2:ℝ)^p*
        (A*(2*C)^(p-2)+B*(cut Q T p)^(p-6)) ≤
      (2*cm+8*(1+14*(h:ℝ))*(2*C*ca+cb))*L^(3*h+3) := by
  have hQp : 0 < Q := by linarith
  have hTp : 0 < T := by linarith
  have hLp : 0 ≤ L := by linarith
  have hCp : 0 ≤ C := by linarith
  have hv : 0 < cut Q T p := cutoff_positive _ _ _ (by positivity) (by norm_num)
  have hratio := MomentGrowthEnvelope.length_ratio_bound Q T p hQ hTp hp hp3 hlen
  have hid : (cut Q T p)^(p-2) = (T/Q^2)^ratioExponent p := by
    simpa only [cut, div_one, ratioExponent] using
      cutoff_small_power (T/Q^2) 1 p (by positivity) (by norm_num)
  have htail : (T/Q^2)*(cut Q T p)^(p-6) = 1 := by
    exact cutoff_tail (T/Q^2) 1 p (by positivity) (by norm_num) (by linarith)
  have hj := band_count Q T p L h C hQ hT hp hp3 hL hC hqlog hclog
  have htwo : (2:ℝ)^p ≤ 8 := by
    calc
      _ ≤ (2:ℝ)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp3
      _ = 8 := by norm_num
  have hCpow : (2*C)^(p-2) ≤ 2*C := by
    calc
      _ ≤ (2*C)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 2*C := Real.rpow_one _
  have hpowers : L^(h+1) ≤ L^(3*h+2) := pow_le_pow_right₀ hL (by omega)
  have hfirst : (cut Q T p)^(p-2)*M ≤ 2*cm*L^(3*h+3) := by
    calc
      _ ≤ (cut Q T p)^(p-2)*(cm*L^(h+1)*(1+T/Q)) := by gcongr
      _ = cm*L^(h+1)*((T/Q^2)^ratioExponent p*(1+T/Q)) := by rw [hid]; ring
      _ ≤ cm*L^(h+1)*2 := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ 2*cm*L^(3*h+3) := by
        have hh := pow_le_pow_right₀ hL (show h+1 ≤ 3*h+3 by omega)
        nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*cm by positivity)]
  have htailbound : B*(cut Q T p)^(p-6) ≤ cb*L^(3*h+2) := by
    calc
      _ ≤ (cb*(T/Q^2)*L^(3*h+2))*(cut Q T p)^(p-6) := by gcongr
      _ = cb*L^(3*h+2)*((T/Q^2)*(cut Q T p)^(p-6)) := by ring
      _ = _ := by rw [htail, mul_one]
  have hbracket : A*(2*C)^(p-2)+B*(cut Q T p)^(p-6) ≤
      (2*C*ca+cb)*L^(3*h+2) := by
    have hh := mul_le_mul ha hCpow (Real.rpow_nonneg (by positivity) _) (by positivity)
    have hh2 := mul_le_mul_of_nonneg_left hpowers (show 0 ≤ 2*C*ca by positivity)
    nlinarith
  have hsecond : bandCountBound (cut Q T p) C*(2:ℝ)^p*
      (A*(2*C)^(p-2)+B*(cut Q T p)^(p-6)) ≤
      8*(1+14*(h:ℝ))*(2*C*ca+cb)*L^(3*h+3) := by
    calc
      _ ≤ ((1+14*(h:ℝ))*L)*8*((2*C*ca+cb)*L^(3*h+2)) := by
        gcongr
      _ = _ := by rw [show 3*h+3 = (3*h+2)+1 by omega, pow_succ]; ring
  nlinarith

#print axioms envelope
run_cmd do
  for t in [``log_two_lower, ``cutoff_log, ``band_count, ``envelope] do
    for ax in (← Lean.collectAxioms t) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {t}"
  Lean.logInfo "LOGARITHMIC MOMENT ENVELOPE: VALID ONLY AFTER SUCCESSFUL COMPILATION"
end SourceLogMomentEnvelope
