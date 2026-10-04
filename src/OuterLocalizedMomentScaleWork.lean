import OuterLocalizedGeometryWork

/-! Selected source blocks retain a cofactor long enough for the proposed
flat eighth-moment length guard. This proves the length guard, not the
logarithmic moment estimate itself. -/
set_option autoImplicit false
noncomputable section
namespace OuterLocalizedMomentScaleWork
open OuterLocalizedGeometryWork OuterActiveDyadicWork OuterSmoothErrorSupportWork
open LongerTupleEncoding

theorem physical_cofactor_logs (X s : ℝ) (hX : 2 ≤ X) (hs : 0 ≤ s)
    (i j : ℕ) (r : Representation) (hr : r ∈ localizedSource X s i j)
    (k : ℕ) (hk : 0 < k) (hlo : X/2 ≤ (index r:ℝ)*k) (hhi : (index r:ℝ)*k ≤ 2*X) :
    (57/250:ℝ)*Real.log X-width X-5*Real.log 2 < Real.log (k:ℝ) ∧
    Real.log (k:ℝ) < (9/35:ℝ)*Real.log X+width X+5*Real.log 2 := by
  have hg := localized_log_geometry X s hX hs i j r hr
  have hm : (0:ℝ) < index r := by
    exact_mod_cast OuterAmbientSizeWork.ambient_index_pos X hX r (localized_subset X s i j hr)
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hx : 0 < X := by linarith
  have h1 := Real.log_le_log (by positivity : 0 < X/2) hlo
  have h2 := Real.log_le_log (mul_pos hm hkR) hhi
  rw [Real.log_mul hm.ne' hkR.ne'] at h1 h2
  rw [Real.log_div hx.ne' (by norm_num)] at h1
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hx.ne'] at h2
  constructor <;> linarith

theorem physical_cofactor_powers (X s : ℝ) (hX : 2 ≤ X) (hs : 0 ≤ s)
    (hlog : 10000 ≤ Real.log X) (i j : ℕ) (r : Representation)
    (hr : r ∈ localizedSource X s i j) (k : ℕ) (hk : 0 < k)
    (hlo : X/2 ≤ (index r:ℝ)*k) (hhi : (index r:ℝ)*k ≤ 2*X) :
    X^(227/1000:ℝ) < (k:ℝ) ∧ (k:ℝ) < X^(129/500:ℝ) := by
  have hh := physical_cofactor_logs X s hX hs i j r hr k hk hlo hhi
  have hw : width X ≤ 1 := by unfold width; apply (div_le_one (by positivity)).mpr; linarith
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hx : 0 < X := by linarith
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  constructor
  · apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hx _) hkR).mp
    rw [Real.log_rpow hx]
    linarith
  · apply (Real.log_lt_log_iff hkR (Real.rpow_pos_of_pos hx _)).mp
    rw [Real.log_rpow hx]
    linarith

theorem flat_eighth_length_saving (X T : ℝ) (k : ℕ) (hX : 1 ≤ X)
    (hk : X^(227/1000:ℝ) ≤ (k:ℝ)) (hT : T ≤ X^(1124/1250:ℝ)) :
    T ≤ (k:ℝ)^4*X^(-11/1250:ℝ) := by
  have hx : 0 < X := by linarith
  have hp : X^(227/250:ℝ) ≤ (k:ℝ)^4 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hx.le _) hk 4
    have he : (X^(227/1000:ℝ))^4 = X^(227/250:ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
      norm_num
    rwa [he] at hh
  calc
    T ≤ X^(1124/1250:ℝ) := hT
    _ = X^(227/250:ℝ)*X^(-11/1250:ℝ) := by rw [← Real.rpow_add hx]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hx.le _)

run_cmd do
  for decl in [``physical_cofactor_logs, ``physical_cofactor_powers,
      ``flat_eighth_length_saving] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterLocalizedMomentScaleWork
