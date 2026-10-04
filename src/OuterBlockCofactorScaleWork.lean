import OuterBlockCofactorWork
import OuterModeCofactorScaleWork

/-! The common cofactor interval for an active block retains the flat
moment's lower scale, and has a fixed endpoint ratio despite rounding. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter OuterSmoothErrorSupportWork
namespace OuterBlockCofactorScaleWork
open OuterBlockCofactorWork OuterActiveDyadicWork OuterSmoothSupportGeometryWork
open OuterLocalizedGeometryWork OuterRectangularBlocksWork LongerTupleEncoding

theorem active_scale (X s : ℝ) (hX : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (i j : ℕ) (k : BlockKey) (hk : k∈activeKeys X s i j) :
    256*(scale k:ℝ)*X^(113/500:ℝ)≤X := by
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hk
  have hloc := active_subset_localized X s i j hr
  have hblock : r∈blockSource X k := Finset.mem_filter.mpr ⟨(active_data X s i j r hr).1,he⟩
  have hg := (localized_log_geometry X s hX hs i j r hloc).2.2
  have hM : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  have hMX : (scale k:ℝ) ≤ index r := by exact_mod_cast (index_range X hX k r hblock).1
  have hlogM := Real.log_le_log hM hMX
  have hw : width X≤1 := by unfold width; apply (div_le_one (by positivity)).mpr; linarith
  have hlog2 : Real.log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlog256 : Real.log 256≤256 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<256)]
  have hXp : 0<X := by linarith
  apply (Real.log_le_log_iff (by positivity : 0<256*(scale k:ℝ)*X^(113/500:ℝ)) hXp).mp
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) hM.ne',Real.log_rpow hXp]
  linarith

theorem lower_half (X : ℝ) (k : BlockKey) (hscale : 256*(scale k:ℝ)≤X) :
    X/(256*(scale k:ℝ))≤(lower X k:ℝ) := by
  have hM : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  have hXp : 0<X := by linarith
  have htwo : (2:ℝ)≤X/(128*(scale k:ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have hf := Nat.lt_floor_add_one (X/(128*(scale k:ℝ)))
  change X/(256*(scale k:ℝ))≤(⌊X/(128*(scale k:ℝ))⌋₊:ℝ)
  have he : X/(256*(scale k:ℝ))=(X/(128*(scale k:ℝ)))/2 := by ring
  rw [he]
  linarith

theorem endpoint_ratio (X : ℝ) (k : BlockKey) (hscale : 256*(scale k:ℝ)≤X) :
    upper X k≤2049*lower X k := by
  have hM : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  have hXp : 0<X := by linarith
  have hlo := lower_half X k hscale
  have hlo1 : (1:ℝ)≤lower X k := by exact_mod_cast lower_pos X k hscale
  have hu : (upper X k:ℝ)<8*X/(scale k:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have he : 2048*(X/(256*(scale k:ℝ)))=8*X/(scale k:ℝ) := by ring
  have hh := mul_le_mul_of_nonneg_left hlo (by norm_num : (0:ℝ)≤2048)
  rw [he] at hh
  exact_mod_cast (show (upper X k:ℝ)≤2049*(lower X k:ℝ) by linarith)

theorem active_lower (X s : ℝ) (hX : 2≤X) (hs : 0≤s) (hlog : 1000000≤Real.log X)
    (i j : ℕ) (k : BlockKey) (hk : k∈activeKeys X s i j) :
    256*(scale k:ℝ)≤X ∧ X^(113/500:ℝ)≤(lower X k:ℝ) ∧ upper X k≤2049*lower X k := by
  have ha := active_scale X s hX hs hlog i j k hk
  have hM : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  have hp : 1≤X^(113/500:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hscale : 256*(scale k:ℝ)≤X := by nlinarith
  refine ⟨hscale,?_,endpoint_ratio X k hscale⟩
  exact ((le_div_iff₀ (by positivity : 0<256*(scale k:ℝ))).mpr (by nlinarith)).trans
    (lower_half X k hscale)

run_cmd do
  for decl in [``active_scale, ``lower_half, ``endpoint_ratio, ``active_lower] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBlockCofactorScaleWork
