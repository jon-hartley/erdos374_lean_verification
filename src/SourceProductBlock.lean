import SourceMixedCoefficient
import SourceLiteralMiddle

/-! v7. Exact mixed polynomial, mass-sensitive energy and frequency blocks.
UNCOMPILED DRAFT. The bound is for the literal three-Mangoldt product and
all time intervals; no moment or first-factor cancellation is assumed.
Countable high-tail assembly is stated separately in the mathematical note. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SourceProductBlock
open SourceMixedCoefficient SourceLiteralMoments SourceLiteralMass SourceMassDischarge
open SourceLiteralMiddle MomentResidualInterval MomentResidualEven
open PositiveInteriorCells PositiveInteriorModel Erdos374.HarmanGram152

theorem triple_physical (X : ℝ) (j : ℕ × ℕ) (p r q : ℕ) (hX : 0 < X)
    (hp : p ∈ support X j 0) (hr : r ∈ support X j 1) (hq : q ∈ support X j 2) :
    X/8 < ((p*(r*q):ℕ):ℝ) ∧ ((p*(r*q):ℕ):ℝ) ≤ 16*X := by
  have hP : 0 < scale j.1 := by unfold scale; positivity
  have hR : 0 < scale j.2 := by unfold scale; positivity
  have hL : 0 < thirdScale X j := by unfold thirdScale; positivity
  have hp' := Finset.mem_Ico.mp hp
  have hr' := Finset.mem_Ico.mp hr
  have hq' := Finset.mem_Ioc.mp hq
  have hp0 : scale j.1 ≤ (p:ℝ) := by simpa [scale] using
    (show (((2:ℕ)^j.1:ℕ):ℝ) ≤ p by exact_mod_cast hp'.1)
  have hp1 : (p:ℝ) ≤ 2*scale j.1 := by simpa [scale] using
    (show (p:ℝ) ≤ (2*(2:ℕ)^j.1:ℕ) by exact_mod_cast hp'.2.le)
  have hr0 : scale j.2 ≤ (r:ℝ) := by simpa [scale] using
    (show (((2:ℕ)^j.2:ℕ):ℝ) ≤ r by exact_mod_cast hr'.1)
  have hr1 : (r:ℝ) ≤ 2*scale j.2 := by simpa [scale] using
    (show (r:ℝ) ≤ (2*(2:ℕ)^j.2:ℕ) by exact_mod_cast hr'.2.le)
  have hq0 : thirdScale X j/8 < (q:ℝ) :=
    (Nat.floor_lt (by positivity : 0 ≤ thirdScale X j/8)).mp hq'.1
  have hq1 : (q:ℝ) ≤ 4*thirdScale X j :=
    (show (q:ℝ) ≤ (⌊4*thirdScale X j⌋₊:ℝ) by exact_mod_cast hq'.2).trans
      (Nat.floor_le (by positivity))
  have hid : scale j.1*scale j.2*thirdScale X j = X := by
    unfold thirdScale
    field_simp
  have hpr0 := mul_le_mul hp0 hr0 hR.le (Nat.cast_nonneg p)
  have hpr1 := mul_le_mul hp1 hr1 (Nat.cast_nonneg r) (by positivity)
  rw [Nat.cast_mul, Nat.cast_mul]
  constructor
  · have ha := mul_lt_mul_of_pos_left hq0 (mul_pos hP hR)
    have hb := mul_le_mul_of_nonneg_right hpr0 (Nat.cast_nonneg q)
    nlinarith
  · have hh := mul_le_mul hpr1 hq1 (Nat.cast_nonneg q) (by positivity)
    nlinarith

theorem coefficient_has_triple (X : ℝ) (j : ℕ × ℕ) (n : ℕ)
    (hn : coefficient X j n ≠ 0) :
    ∃ p ∈ support X j 0, ∃ r ∈ support X j 1, ∃ q ∈ support X j 2,
      p*(r*q)=n := by
  change (array (support X j 0) *
    (array (support X j 1)*array (support X j 2))) n ≠ 0 at hn
  rw [ArithmeticFunction.mul_apply] at hn
  obtain ⟨ab, hab, hnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hp := array_mem _ _ (mul_ne_zero_iff.mp hnz).1
  have hbc := (mul_ne_zero_iff.mp hnz).2
  rw [ArithmeticFunction.mul_apply] at hbc
  obtain ⟨cd, hcd, hcz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hbc
  refine ⟨ab.1, hp, cd.1, array_mem _ _ (mul_ne_zero_iff.mp hcz).1,
    cd.2, array_mem _ _ (mul_ne_zero_iff.mp hcz).2, ?_⟩
  rw [(Nat.mem_divisorsAntidiagonal.mp hcd).1]
  exact (Nat.mem_divisorsAntidiagonal.mp hab).1

theorem top_cast_le (X : ℝ) (j : ℕ × ℕ) (hX : 0 < X) :
    (totalTop X j:ℝ) ≤ 16*X := by
  have hP : 0 < scale j.1 := by unfold scale; positivity
  have hR : 0 < scale j.2 := by unfold scale; positivity
  have hL : 0 < thirdScale X j := by unfold thirdScale; positivity
  have hf := Nat.floor_le (show 0 ≤ 4*thirdScale X j by positivity)
  change (((2*2^j.1)*((2*2^j.2)*⌊4*thirdScale X j⌋₊):ℕ):ℝ) ≤ _
  push_cast
  change (2*scale j.1)*((2*scale j.2)*(⌊4*thirdScale X j⌋₊:ℝ)) ≤ _
  calc
    _ ≤ (2*scale j.1)*((2*scale j.2)*(4*thirdScale X j)) := by gcongr
    _ = _ := by unfold thirdScale; field_simp <;> ring

theorem source_energy (X : ℝ) (j : ℕ × ℕ)
    (hX : 2 ≤ X) (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X)) :
    (∑ n ∈ Finset.Ioc 0 (totalTop X j), ‖coefficient X j n‖^2/(n:ℝ)^2) ≤
      27000*(Real.log (16*X))^3/X := by
  have hXp : 0 < X := by linarith
  have hnonneg : 0 ≤ Real.log (16*X) := Real.log_nonneg (by linarith)
  have hh := energy_from_mass (Finset.Ioc 0 (totalTop X j)) (coefficient X j)
    X ((Real.log (16*X))^3) 3375 hXp (by positivity)
    (by
      intro n _ hn
      obtain ⟨p,hp,r,hr,q,hq,he⟩ := coefficient_has_triple X j n hn
      rw [←he]
      exact (triple_physical X j p r q hXp hp hr hq).1.le)
    (by
      intro n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
      have hnu : (n:ℝ) ≤ 16*X :=
        (show (n:ℝ) ≤ (totalTop X j:ℝ) by exact_mod_cast (Finset.mem_Ioc.mp hn).2).trans
          (top_cast_le X j hXp)
      exact (coefficient_log_cap X j n).trans
        (pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by
          have := (Finset.mem_Ioc.mp hn).1; omega)))
          (Real.log_le_log hn0 hnu) 3))
    (coefficient_mass X j hX hlog hj)
  convert hh using 1 <;> ring

theorem array_dirichlet (X : ℝ) (j : ℕ × ℕ) (i : Fin 3) (t : ℝ) :
    finiteDirichlet (top X j i) (array (support X j i))
      (-((1:ℂ)+Complex.I*(t:ℂ))) = factor X j i t := by
  unfold finiteDirichlet factor verticalDirichlet152
  have hs : support X j i ⊆ Finset.Ioc 0 (top X j i) := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨support_pos X j i n hn, support_le_top X j i n hn⟩
  calc
    _ = ∑ n ∈ support X j i, array (support X j i) n *
        (n:ℂ)^(-((1:ℂ)+Complex.I*(t:ℂ))) := by
      symm
      apply Finset.sum_subset hs
      intro n _ hn
      simp [array, restricted, hn]
    _ = _ := Finset.sum_congr rfl (by intro n hn; simp [array, restricted, hn])

theorem product_eq_collected (X : ℝ) (j : ℕ × ℕ) (t : ℝ)
    (hX : 2 ≤ X) (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X)) :
    sourceProduct X j t = verticalDirichlet152 (Finset.Ioc 0 (totalTop X j))
      (coefficient X j) 1 t := by
  have hN := top_pos X j 0 hX hlog hj
  have hM := top_pos X j 1 hX hlog hj
  have hL := top_pos X j 2 hX hlog hj
  have hb := finiteDirichlet_mul (top X j 1) (top X j 2) hM hL
    (array (support X j 1)) (array (support X j 2))
    (array_vanishes X j 1) (array_vanishes X j 2) (-((1:ℂ)+Complex.I*(t:ℂ)))
  have ha := finiteDirichlet_mul (top X j 0) (top X j 1*top X j 2) hN (by nlinarith)
    (array (support X j 0)) (array (support X j 1)*array (support X j 2))
    (array_vanishes X j 0)
    (mul_vanishes _ _ _ _ (array_vanishes X j 1) (array_vanishes X j 2))
    (-((1:ℂ)+Complex.I*(t:ℂ)))
  rw [hb, array_dirichlet, array_dirichlet, array_dirichlet] at ha
  simpa only [sourceProduct, mul_assoc, totalTop, finiteDirichlet,
    verticalDirichlet152, coefficient, Complex.ofReal_one] using ha.symm

def blockConstant : ℝ := 600000000

/-- All real starting positions and all T>=0, with log^4 rather than log^7 loss. -/
theorem source_block (X a T : ℝ) (j : ℕ × ℕ)
    (hX : 2 ≤ X) (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X))
    (hT : 0 ≤ T) :
    (∫ t in Icc a (a+T), ‖sourceProduct X j t‖^2) ≤
      blockConstant*(1+Real.log X)^4*(T/X+1) := by
  let N := totalTop X j
  let W := 1+Real.log X
  have hXp : 0 < X := by linarith
  have hW : 1 ≤ W := by dsimp [W]; linarith [Real.log_nonneg (show 1 ≤ X by linarith)]
  have hN : 1 ≤ N := by
    have h0 := top_pos X j 0 hX hlog hj
    have h1 := top_pos X j 1 hX hlog hj
    have h2 := top_pos X j 2 hX hlog hj
    dsimp [N, totalTop]
    exact Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNX : (N:ℝ) ≤ 16*X := top_cast_le X j hXp
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hlog16 : Real.log (16*X) ≤ 4*W := by
    rw [Real.log_mul (by norm_num : (16:ℝ)≠0) hXp.ne',
      show (16:ℝ)=2^4 by norm_num, Real.log_pow]
    dsimp [W]
    nlinarith [Real.log_nonneg (show 1 ≤ X by linarith)]
  have hlogN : 1+Real.log (N:ℝ) ≤ 5*W := by
    have hh := Real.log_le_log (by linarith : (0:ℝ)<N) hNX
    linarith
  have he : (∑ n ∈ Finset.Ioc 0 N, ‖coefficient X j n‖^2/(n:ℝ)^2) ≤
      1728000*W^3/X := by
    apply (source_energy X j hX hlog hj).trans
    have hh := pow_le_pow_left₀ (Real.log_nonneg (show 1 ≤ 16*X by linarith)) hlog16 3
    have hd := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤27000)) hXp.le
    convert hd using 1 <;> ring
  have hm := weighted_normalized_mean_square (Finset.Ioc 0 N) (coefficient X j) N hN
    (by intro n hn; exact ⟨by have := (Finset.mem_Ioc.mp hn).1; omega,
      (Finset.mem_Ioc.mp hn).2⟩) 1 (by norm_num) _ he a (a+T) (by linarith)
  simp only [add_sub_cancel_left] at hm
  have hbr : T+4*(N:ℝ)*(1+Real.log (N:ℝ)) ≤ T+320*X*W := by
    have hh := mul_le_mul hNX hlogN
      (show 0 ≤ 1+Real.log (N:ℝ) by linarith [Real.log_nonneg hNr]) (by positivity)
    nlinarith
  have hbound : (T+320*X*W)*(1728000*W^3/X) ≤
      blockConstant*W^4*(T/X+1) := by
    have htq : 0 ≤ T/X := div_nonneg hT hXp.le
    have hw3 : 0 ≤ W^3 := by positivity
    have hp : W^3 ≤ W^4 := pow_le_pow_right₀ hW (by decide : 3≤4)
    have hh := mul_le_mul_of_nonneg_right hp htq
    have hid : (T+320*X*W)*(1728000*W^3/X) =
        1728000*(W^3*(T/X)+320*W^4) := by field_simp <;> ring
    rw [hid]
    unfold blockConstant
    nlinarith [sq_nonneg (W^2)]
  simp_rw [product_eq_collected X j _ hX hlog hj]
  exact hm.trans ((mul_le_mul_of_nonneg_right hbr (by positivity)).trans hbound)

/-- One weighted high-frequency block, for the original product. -/
theorem weighted_source_block (X T : ℝ) (j : ℕ × ℕ)
    (hX : 2 ≤ X) (hlog : 1000000 ≤ Real.log X) (hj : j ∈ boxes (mesh X))
    (hT : 0 < T) :
    (∫ t in Icc T (2*T), ‖sourceProduct X j t‖^2/t^2) ≤
      blockConstant*(1+Real.log X)^4*(1/(X*T)+1/T^2) := by
  have hc : Continuous (fun t => ‖sourceProduct X j t‖^2) :=
    (((factor_continuous X j 0).mul (factor_continuous X j 1)).mul
      (factor_continuous X j 2)).norm.pow 2
  have hd : ContinuousOn (fun t : ℝ => ‖sourceProduct X j t‖^2/t^2) (Icc T (2*T)) :=
    hc.continuousOn.div (continuous_id.pow 2).continuousOn
      (by intro t ht; have hp : 0<t := hT.trans_le ht.1; positivity)
  have hi : IntegrableOn (fun t : ℝ => ‖sourceProduct X j t‖^2/t^2) (Icc T (2*T)) :=
    hd.integrableOn_compact isCompact_Icc
  have hm := setIntegral_mono_on hi
    (hc.integrableOn_Icc.div_const (T^2)) measurableSet_Icc (by
      intro t ht
      apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hT)
      exact pow_le_pow_left₀ hT.le ht.1 2)
  rw [integral_div] at hm
  have hb := source_block X T T j hX hlog hj hT.le
  rw [show T+T=2*T by ring] at hb
  apply hm.trans
  have hquot := div_le_div_of_nonneg_right hb (sq_nonneg T)
  convert hquot using 1 <;> field_simp <;> ring

#print axioms source_energy
#print axioms product_eq_collected
#print axioms weighted_source_block
run_cmd do
  for n in [``triple_physical, ``coefficient_has_triple, ``top_cast_le,
      ``source_energy, ``array_dirichlet, ``product_eq_collected,
      ``source_block, ``weighted_source_block] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "V7 ACTUAL HIGH-FREQUENCY BLOCKS: VALID ONLY AFTER COMPILATION"
end SourceProductBlock
