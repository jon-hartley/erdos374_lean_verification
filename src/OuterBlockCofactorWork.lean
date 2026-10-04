import OuterRectangularBlocksWork
import ContinuousCofactorMellin
import MellinSmoothingFunction

/-! A single finite cofactor interval for each rectangular source block.
It covers both the literal moving window and its smoothed continuous main term. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Set
namespace OuterBlockCofactorWork
open OuterActiveDyadicWork OuterRectangularBlocksWork OuterSourceReindexWork
open OuterSmoothErrorSupportWork LongerTupleEncoding

def scale (k : BlockKey) : ℕ := 2^k.1*2^k.2.1*2^k.2.2.1*2^k.2.2.2

def lower (X : ℝ) (k : BlockKey) : ℕ := ⌊X/(128*(scale k:ℝ))⌋₊
def upper (X : ℝ) (k : BlockKey) : ℕ := ⌈8*X/(scale k:ℝ)⌉₊

theorem scale_pos (k : BlockKey) : 0<scale k := by unfold scale; positivity

theorem index_range (X : ℝ) (hX : 2≤X) (k : BlockKey) (r : Representation)
    (hr : r∈blockSource X k) : scale k ≤ index r ∧ index r<16*scale k := by
  have hd := ambient_data X hX r (Finset.mem_filter.mp hr).1
  have he := (Finset.mem_filter.mp hr).2
  have hb (n j : ℕ) (hn : 0<n) (hj : n.log2=j) : 2^j≤n ∧ n<2*2^j := by
    have hl := Nat.log2_self_le (Nat.ne_of_gt hn)
    have hu := Nat.lt_log2_self (n:=n)
    rw [hj] at hl hu
    rw [Nat.pow_succ] at hu
    exact ⟨hl,by omega⟩
  have hp := hb r.1 k.1 hd.2.2.1 (congrArg (fun z : BlockKey => z.1) he)
  have hdiv := hb (drop r).1 k.2.1 hd.2.2.2.2.1 (congrArg (fun z : BlockKey => z.2.1) he)
  have ha := hb (drop r).2.1 k.2.2.1 hd.2.2.2.2.2.1 (congrArg (fun z : BlockKey => z.2.2.1) he)
  have hb' := hb (drop r).2.2 k.2.2.2 hd.2.2.2.2.2.2 (congrArg (fun z : BlockKey => z.2.2.2) he)
  have hid : index r=r.1*(drop r).1*(drop r).2.1*(drop r).2.2 := by
    conv_lhs => rw [←rebuild_drop r hd.1]
    simp [index,rebuild,Nat.mul_assoc]
  rw [hid]
  constructor
  · exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp.1 hdiv.1) ha.1) hb'.1
  · have hh := Nat.mul_lt_mul_of_pos_left hb'.2
      (Nat.mul_pos (Nat.mul_pos hd.2.2.1 hd.2.2.2.2.1) hd.2.2.2.2.2.1)
    have hu := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp.2.le hdiv.2.le) ha.2.le) (le_refl (2*2^k.2.2.2))
    exact hh.trans_le (hu.trans_eq (by unfold scale; ring))

theorem lower_pos (X : ℝ) (k : BlockKey) (hX : 256*(scale k:ℝ)≤X) :
    1≤lower X k := by
  have hM : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  have hXp : 0<X := by linarith
  apply (Nat.le_floor_iff (by positivity : 0≤X/(128*(scale k:ℝ)))).mpr
  rw [Nat.cast_one]
  apply (le_div_iff₀ (by positivity)).mpr
  linarith

theorem margins (X x δ ε : ℝ) (k : BlockKey) (m : ℕ)
    (hX : 0<X) (hx : x∈Icc X (2*X)) (hδ : δ∈Icc 0 (1/2))
    (hε : ε∈Ioo 0 (1/4)) (hm : scale k≤m ∧ m≤16*scale k) :
    (m:ℝ)*lower X k/x ≤ 1-Real.log 2*ε ∧
    (m:ℝ)*lower X k/(x-x*δ) ≤ 1-Real.log 2*ε ∧
    1+2*Real.log 2*ε ≤ (m:ℝ)*upper X k/x ∧
    1+2*Real.log 2*ε ≤ (m:ℝ)*upper X k/(x-x*δ) := by
  have hM : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  have hmL : (scale k:ℝ)≤m := by exact_mod_cast hm.1
  have hmU : (m:ℝ)≤16*(scale k:ℝ) := by exact_mod_cast hm.2
  have hl : (lower X k:ℝ)≤X/(128*(scale k:ℝ)) := Nat.floor_le (by positivity)
  have hu : 8*X/(scale k:ℝ)≤upper X k := Nat.le_ceil _
  have hl' := (le_div_iff₀ (by positivity : 0<128*(scale k:ℝ))).mp hl
  have hu' := (div_le_iff₀ hM).mp hu
  have hml := mul_le_mul_of_nonneg_right hmU (Nat.cast_nonneg (lower X k))
  have hmu := mul_le_mul_of_nonneg_right hmL (Nat.cast_nonneg (upper X k))
  have hxp : 0<x := hX.trans_le hx.1
  have hleft : X/2≤x-x*δ := (DyadicDivisorWindow.window_bounds X x δ hX hx hδ).1
  have hleftp : 0<x-x*δ := by linarith
  have hleftle : x-x*δ≤x := by nlinarith [hδ.1]
  have hlog2 : Real.log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlogε := mul_le_mul_of_nonneg_right hlog2 hε.1.le
  have hlow : (1/2:ℝ)≤1-Real.log 2*ε := by linarith [hε.2]
  have hhigh : 1+2*Real.log 2*ε≤2 := by linarith [hε.2]
  refine ⟨le_trans ?_ hlow,le_trans ?_ hlow,le_trans hhigh ?_,le_trans hhigh ?_⟩
  · apply (div_le_iff₀ hxp).mpr; nlinarith [hx.1]
  · apply (div_le_iff₀ hleftp).mpr; nlinarith
  · apply (le_div_iff₀ hxp).mpr; nlinarith [hx.2]
  · apply (le_div_iff₀ hleftp).mpr; nlinarith [hx.2]

theorem lower_le_upper (X : ℝ) (k : BlockKey) (hX : 0<X) : lower X k≤upper X k := by
  have hM : (0:ℝ)<scale k := by exact_mod_cast scale_pos k
  have hl : (lower X k:ℝ)≤X/(128*(scale k:ℝ)) := Nat.floor_le (by positivity)
  have hu : 8*X/(scale k:ℝ)≤upper X k := Nat.le_ceil _
  have hmid : X/(128*(scale k:ℝ))≤8*X/(scale k:ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hM).mpr
    nlinarith [mul_pos hX hM]
  exact_mod_cast hl.trans (hmid.trans hu)

run_cmd do
  for decl in [``scale_pos, ``index_range, ``lower_pos, ``margins, ``lower_le_upper] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBlockCofactorWork
