import OuterCompletedIntervalWork

/-! Exact logarithmic forms of the outer-prime masks. Every displayed
inequality is affine in the logarithms of the individual factors; strict
and non-strict endpoints are preserved. No Fourier approximation is used. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace OuterPairLogConstraintsWork
open SieveGeometricGrid SieveWeightedCutoffs SieveBoxedFamily
open LongerTupleEncoding OuterCompletedIntervalWork

theorem div_rpow_le_iff (H p a e : ℝ) (hH : 0<H) (hp : 0<p) (ha : 0<a) :
    (H/p)^e ≤ a ↔ e*Real.log H ≤ e*Real.log p+Real.log a := by
  have hD : 0<H/p := div_pos hH hp
  rw [←Real.log_le_log_iff (Real.rpow_pos_of_pos hD e) ha,
    Real.log_rpow hD,Real.log_div (ne_of_gt hH) (ne_of_gt hp)]
  constructor <;> intro hh <;> nlinarith

theorem lt_div_rpow_iff (H p a e : ℝ) (hH : 0<H) (hp : 0<p) (ha : 0<a) :
    a < (H/p)^e ↔ e*Real.log p+Real.log a < e*Real.log H := by
  have hD : 0<H/p := div_pos hH hp
  rw [←Real.log_lt_log_iff ha (Real.rpow_pos_of_pos hD e),
    Real.log_rpow hD,Real.log_div (ne_of_gt hH) (ne_of_gt hp)]
  constructor <;> intro hh <;> nlinarith

theorem inBox_log_iff (X s p a : ℝ) (i : ℕ) (hX : 0<X) (hp : 0<p) (ha : 0<a) :
    InBox (level X s/p) s a i ↔
      exponent s i*((1-3*s)*Real.log X) ≤ exponent s i*Real.log p+Real.log a ∧
      exponent s (i+1)*Real.log p+Real.log a < exponent s (i+1)*((1-3*s)*Real.log X) := by
  have hH : 0<level X s := Real.rpow_pos_of_pos hX _
  unfold InBox scale
  rw [div_rpow_le_iff _ _ _ _ hH hp ha,lt_div_rpow_iff _ _ _ _ hH hp ha]
  simp only [level,Real.log_rpow hX]

theorem pool_log_iff (X s : ℝ) (p a : ℕ) (hX : 0<X) (hp : 0<p) (ha : 0<a) :
    a∈pool (level X s/p) s (cutoffThree X s p) ↔
      a.Prime ∧ Real.log (p:ℝ)+3*Real.log (a:ℝ) < (1-3*s)*Real.log X ∧
      s^2*((1-3*s)*Real.log X) ≤ s^2*Real.log (p:ℝ)+Real.log (a:ℝ) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hH : 0<level X s := Real.rpow_pos_of_pos hX _
  rw [mem_pool]
  unfold cutoffThree
  rw [lt_div_rpow_iff _ _ _ _ hH hpR haR,div_rpow_le_iff _ _ _ _ hH hpR haR]
  simp only [level,Real.log_rpow hX]
  constructor
  · rintro ⟨hprime,hu,hl⟩
    exact ⟨hprime,by linarith,hl⟩
  · rintro ⟨hprime,hu,hl⟩
    exact ⟨hprime,by linarith,hl⟩

theorem log_index (p d a b : ℕ) (hp : 0<p) (hd : 0<d) (ha : 0<a) (hb : 0<b) :
    Real.log (index (p,d,[a,b]):ℝ) =
      Real.log (p:ℝ)+Real.log (d:ℝ)+Real.log (a:ℝ)+Real.log (b:ℝ) := by
  have hpR : (p:ℝ)≠0 := by exact_mod_cast (ne_of_gt hp)
  have hdR : (d:ℝ)≠0 := by exact_mod_cast (ne_of_gt hd)
  have haR : (a:ℝ)≠0 := by exact_mod_cast (ne_of_gt ha)
  have hbR : (b:ℝ)≠0 := by exact_mod_cast (ne_of_gt hb)
  simp [index,Real.log_mul,hpR,hdR,haR,hbR,add_assoc]

theorem product_lower_log_iff (X e : ℝ) (p d a b : ℕ) (hX : 0<X)
    (hp : 0<p) (hd : 0<d) (ha : 0<a) (hb : 0<b) :
    X^e < (index (p,d,[a,b]):ℝ) ↔
      e*Real.log X < Real.log (p:ℝ)+Real.log (d:ℝ)+Real.log (a:ℝ)+Real.log (b:ℝ) := by
  have hi : (0:ℝ) < index (p,d,[a,b]) := by
    simp only [index,List.prod_cons,List.prod_nil,Nat.cast_mul,Nat.cast_one]
    positivity
  rw [←Real.log_lt_log_iff (Real.rpow_pos_of_pos hX e) hi,
    Real.log_rpow hX,log_index p d a b hp hd ha hb]

theorem completedWindow_log_iff (p d a b k : ℕ) (L R : ℝ)
    (hp : 0<p) (hd : 0<d) (ha : 0<a) (hb : 0<b) (hk : 0<k)
    (hL : 0<L) (hR : 0<R) :
    completedWindow d a b k L R p ↔
      Real.log L < Real.log (p:ℝ)+Real.log (d:ℝ)+Real.log (a:ℝ)+Real.log (b:ℝ)+Real.log (k:ℝ) ∧
      Real.log (p:ℝ)+Real.log (d:ℝ)+Real.log (a:ℝ)+Real.log (b:ℝ)+Real.log (k:ℝ) ≤ Real.log R := by
  have hi : (0:ℝ) < index (p,d,[a,b]) := by
    simp only [index,List.prod_cons,List.prod_nil,Nat.cast_mul,Nat.cast_one]
    positivity
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hn : (0:ℝ)<(index (p,d,[a,b])*k:ℕ) := by
    simpa only [Nat.cast_mul] using mul_pos hi hkR
  unfold completedWindow
  rw [←Real.log_lt_log_iff hL hn,←Real.log_le_log_iff hn hR]
  simp only [Nat.cast_mul,
    Real.log_mul (ne_of_gt hi) (ne_of_gt hkR),log_index p d a b hp hd ha hb]

run_cmd do
  for decl in [``div_rpow_le_iff, ``lt_div_rpow_iff, ``inBox_log_iff,
      ``pool_log_iff, ``log_index, ``product_lower_log_iff, ``completedWindow_log_iff] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairLogConstraintsWork
