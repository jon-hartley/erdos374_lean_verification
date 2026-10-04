import Item1ZetaContourGeometry
import Item1SmoothCapScalar

/-! Original envelope definitions and scalar estimates, kept under their
original namespace. No analytic estimate is assumed in this helper. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Item1SharpCapEnvelope
open Item1ZetaContourGeometry Item1SmoothCapScalar

/-- Smoothing width, unrelated to the physical half-width. -/
def smoothing (B : ℕ) (ell : ℝ) : ℝ := 1/ell^(B+2)

def envelope (ell N δ a C R t : ℝ) : ℝ :=
  12*δ*ell+4*ell/N+
  9*C*R^9*Real.exp (-a*ell/R^(3/4:ℝ))/δ+
  216*C*R^9/(δ*t^2)+324*ell^2/(δ*t)

theorem smoothing_range (B : ℕ) (ell : ℝ) (hl : 2 ≤ ell) :
    0 < smoothing B ell ∧ smoothing B ell ≤ 1/2 := by
  have hlp : 0<ell := by linarith
  have hp : 2 ≤ ell^(B+2) := hl.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ (show 1≤ell by linarith)
      (show 1≤B+2 by omega))
  refine ⟨by unfold smoothing; positivity,?_⟩
  exact one_div_le_one_div_of_le (by norm_num) hp

theorem height_log_upper (N t : ℝ) (hN : 0 < N) (hl : 2 ≤ Real.log N)
    (ht : 0 < t) (htu : t ≤ N^3) : heightLog t ≤ 4*Real.log N := by
  have hh := Real.log_le_log (show 0<2*t by positivity)
    (mul_le_mul_of_nonneg_left htu (by norm_num : (0:ℝ)≤2))
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (pow_ne_zero _ hN.ne'),Real.log_pow] at hh
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  unfold heightLog
  norm_num at hh h2
  linarith

/-- The subcritical strip gives a positive fourth-root logarithmic saving. -/
theorem depth_saving (ell R a : ℝ) (hl : 1 ≤ ell) (hR : 0 < R)
    (hu : R ≤ 4*ell) (ha : 0 ≤ a) :
    Real.exp (-a*ell/R^(3/4:ℝ)) ≤ Real.exp (-(a/4)*ell^(1/4:ℝ)) := by
  have hlp : 0<ell := by linarith
  have hquarter : ell^(1/4:ℝ)*ell^(3/4:ℝ)=ell := by
    rw [←Real.rpow_add hlp]
    norm_num
  have hfour : (4:ℝ)^(3/4:ℝ) ≤ 4 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hp : R^(3/4:ℝ) ≤ 4*ell^(3/4:ℝ) := by
    have hh := Real.rpow_le_rpow hR.le hu (by norm_num : (0:ℝ)≤3/4)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) hlp.le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hlp.le _))
  have hmult := mul_le_mul_of_nonneg_left hp
    (show 0≤(a/4)*ell^(1/4:ℝ) by positivity)
  have hc : (a/4)*ell^(1/4:ℝ) * (4*ell^(3/4:ℝ)) = a*ell := by
    calc
      _ = a*(ell^(1/4:ℝ)*ell^(3/4:ℝ)) := by ring
      _ = _ := by rw [hquarter]
  rw [hc] at hmult
  have hs : (a/4)*ell^(1/4:ℝ) ≤ a*ell/R^(3/4:ℝ) :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hR _)).mpr hmult
  exact Real.exp_le_exp.mpr (by simpa only [neg_mul,neg_div] using neg_le_neg hs)

/-- Pure monomial identities: the scalar exponents are not heuristic log losses. -/
theorem monomial_normalizations (B : ℕ) (ell t : ℝ) (hl : 0 < ell) (ht : 0 < t) :
    (12*smoothing B ell*ell)*ell^B = 12/ell ∧
    (324*ell^2/(smoothing B ell*t))*ell^B = 324*ell^(2*B+4)/t ∧
    ell^9/smoothing B ell*ell^B = ell^(2*B+11) := by
  unfold smoothing
  constructor
  · field_simp
    simp only [pow_add]
    ring
  constructor
  · field_simp
    simp only [Nat.mul_comm 2 B,pow_add,pow_mul]
    ring
  · field_simp
    simp only [Nat.mul_comm 2 B,pow_add,pow_mul]
    ring

/-- Both horizontal and right-tail divisions use the SAME lower cutoff. -/
theorem frequency_divisions (B : ℕ) (ell t : ℝ) (hl : 1 ≤ ell)
    (ht : ell^(2*B+6) ≤ t) :
    ell^(2*B+11)/t^2 ≤ 1/ell^(2*B+1) ∧
      ell^(2*B+4)/t ≤ 1/ell^2 := by
  have hlp : 0<ell := by linarith
  have htp : 0<t := (pow_pos hlp _).trans_le ht
  have ht2 := pow_le_pow_left₀ (pow_nonneg hlp.le _) ht 2
  constructor
  · apply (div_le_div_iff₀ (sq_pos_of_pos htp) (pow_pos hlp _)).mpr
    have hid : ell^(2*B+11)*ell^(2*B+1) = (ell^(2*B+6))^2 := by
      rw [←pow_add,←pow_mul]
      congr 1
      omega
    simpa only [one_mul,hid] using ht2
  · apply (div_le_div_iff₀ htp (sq_pos_of_pos hlp)).mpr
    have hid : ell^(2*B+4)*ell^2 = ell^(2*B+6) := by
      rw [←pow_add]
    simpa only [one_mul,hid] using ht

/-- Each of the five actual errors is dominated by the retained scalar envelope. -/
theorem normalized_envelope (B : ℕ) (ell N a C R t : ℝ)
    (hl : 2 ≤ ell) (hN : N=Real.exp ell) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hR : 0<R) (hRu : R≤4*ell) (ht : ell^(2*B+6)≤t) :
    envelope ell N (smoothing B ell) a C R t * ell^B ≤ normalizedBudget B a C ell := by
  have hlp : 0<ell := by linarith
  have hl1 : 1≤ell := by linarith
  have htp : 0<t := (pow_pos hlp _).trans_le ht
  have hδ := (smoothing_range B ell hl).1
  obtain ⟨hid1,hid5,hid3⟩ := monomial_normalizations B ell t hlp htp
  obtain ⟨hf4,hf5⟩ := frequency_divisions B ell t hl1 ht
  have hRp : R^9 ≤ (4:ℝ)^9*ell^9 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hR.le hRu 9
  have hex := depth_saving ell R a hl1 hR hRu ha
  have h2 : (4*ell/N)*ell^B = 4*(Real.exp (-ell)*ell^(B+1)) := by
    rw [hN,Real.exp_neg]
    simp only [pow_add,pow_one]
    ring
  have h3 : (9*C*R^9*Real.exp (-a*ell/R^(3/4:ℝ))/smoothing B ell)*ell^B ≤
      (9*(4:ℝ)^9*C)*(Real.exp (-(a/4)*ell^(1/4:ℝ))*ell^(2*B+11)) := by
    have hm := mul_le_mul hRp hex (Real.exp_pos _).le (by positivity)
    have hh := mul_le_mul_of_nonneg_left hm
      (show 0≤9*C*ell^B/smoothing B ell by positivity)
    have heq : (9*C*ell^B/smoothing B ell)*
        ((4:ℝ)^9*ell^9*Real.exp (-(a/4)*ell^(1/4:ℝ))) =
        (9*(4:ℝ)^9*C)*(Real.exp (-(a/4)*ell^(1/4:ℝ))*ell^(2*B+11)) := by
      calc
        _ = (9*(4:ℝ)^9*C)*Real.exp (-(a/4)*ell^(1/4:ℝ))*
          (ell^9/smoothing B ell*ell^B) := by ring
        _ = _ := by rw [hid3]; ring
    rw [heq] at hh
    convert hh using 1 <;> ring
  have h4 : (216*C*R^9/(smoothing B ell*t^2))*ell^B ≤
      (216*(4:ℝ)^9*C)/ell^(2*B+1) := by
    have hh := mul_le_mul_of_nonneg_left hRp
      (show 0≤216*C*ell^B/(smoothing B ell*t^2) by positivity)
    have hf := mul_le_mul_of_nonneg_left hf4
      (show 0≤216*(4:ℝ)^9*C by positivity)
    have hid : (216*C*ell^B/(smoothing B ell*t^2))*((4:ℝ)^9*ell^9) =
        (216*(4:ℝ)^9*C)*(ell^(2*B+11)/t^2) := by
      calc
        _ = (216*(4:ℝ)^9*C)*(ell^9/smoothing B ell*ell^B)/t^2 := by ring
        _ = _ := by rw [hid3]; ring
    rw [hid] at hh
    have hh' : (216*C*R^9/(smoothing B ell*t^2))*ell^B ≤
        (216*(4:ℝ)^9*C)*(ell^(2*B+11)/t^2) := by
      convert hh using 1 <;> ring
    exact hh'.trans (by simpa only [mul_one_div] using hf)
  have h5 : (324*ell^2/(smoothing B ell*t))*ell^B ≤ 324/ell^2 := by
    rw [hid5]
    simpa only [mul_div_assoc,mul_one_div] using
      mul_le_mul_of_nonneg_left hf5 (by norm_num : (0:ℝ)≤324)
  unfold envelope normalizedBudget
  rw [add_mul,add_mul,add_mul,add_mul,hid1,h2]
  exact add_le_add (add_le_add (add_le_add (le_refl _) h3) h4) h5

end Item1SharpCapEnvelope

run_cmd do
  for target in [
    ``Item1SharpCapEnvelope.smoothing_range,
    ``Item1SharpCapEnvelope.height_log_upper,
    ``Item1SharpCapEnvelope.depth_saving,
    ``Item1SharpCapEnvelope.monomial_normalizations,
    ``Item1SharpCapEnvelope.frequency_divisions,
    ``Item1SharpCapEnvelope.normalized_envelope] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "SCALAR ENVELOPE PASSED: six original theorem guards."
