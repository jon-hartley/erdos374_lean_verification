import LongPairSeparatedCoreWork
import SieveDivisorWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact prime/composite split of the completed cofactor d*k in the
literal separated core. All source filters and signed small weights stay
in place. The composite count is retained; no mean bound is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LongPairCofactorSwitchWork
open LongerTupleEncoding LongerTupleActualProfiles LongPairCloseDistinctMeanWork
open UpperAfter545Remaining

def realWeight (X s : ℝ) (r : Representation) : ℝ :=
  (originalWeight X s true r).re

def cofactorWindow (r : Representation) (L R : ℝ) : Finset ℕ :=
  FiniteSieveWindow.window (L/index r) (R/index r)

def primeCofactorCount (X s L R : ℝ) : ℝ :=
  ∑ r ∈ (separatedSource X s).filter (fun r => r.2.1=1),
    ((FiniteSieveWindow.primeWindow (L/index r) (R/index r)).card : ℝ)

def compositeCofactorCount (X s L R : ℝ) : ℝ :=
  ∑ r ∈ separatedSource X s, realWeight X s r *
    ∑ k ∈ cofactorWindow r L R, if ¬Nat.Prime (r.2.1*k) then (1 : ℝ) else 0

def sourceMass (X s : ℝ) : ℝ :=
  ∑ r ∈ separatedSource X s, realWeight X s r / index r

theorem realWeight_one (X s : ℝ) (r : Representation) (hd : r.2.1=1) :
    realWeight X s r=1 := by
  simp [realWeight, originalWeight, hd, SieveSmallWeights.weight_one]

theorem window_cofactor_one_lt (r : Representation) (L R : ℝ)
    (hi : 0 < index r) (hL : (index r : ℝ) ≤ L) (k : ℕ)
    (hk : k ∈ cofactorWindow r L R) : 1 < k := by
  have hip : (0 : ℝ) < index r := by exact_mod_cast hi
  have hLdiv : 1 ≤ L/index r := (le_div_iff₀ hip).mpr (by simpa using hL)
  have hf : 1 ≤ ⌊L/index r⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hLdiv)
  have hh := (Finset.mem_Ioc.mp hk).1
  omega

theorem completed_prime_iff (r : Representation) (L R : ℝ)
    (hi : 0 < index r) (hL : (index r : ℝ) ≤ L) (k : ℕ)
    (hk : k ∈ cofactorWindow r L R) :
    Nat.Prime (r.2.1*k) ↔ r.2.1=1 ∧ Nat.Prime k := by
  have hk1 := window_cofactor_one_lt r L R hi hL k hk
  rw [Nat.prime_mul_iff]
  constructor
  · rintro (⟨_, he⟩ | ⟨hp, hd⟩)
    · omega
    · exact ⟨hd, hp⟩
  · rintro ⟨hd, hp⟩
    exact Or.inr ⟨hp, hd⟩

theorem prime_window_sum (X s L R : ℝ) (r : Representation)
    (hi : 0 < index r) (hL : (index r : ℝ) ≤ L) :
    realWeight X s r *
      (∑ k ∈ cofactorWindow r L R, if Nat.Prime (r.2.1*k) then (1 : ℝ) else 0) =
        if r.2.1=1 then
          ((FiniteSieveWindow.primeWindow (L/index r) (R/index r)).card : ℝ) else 0 := by
  by_cases hd : r.2.1=1
  · rw [ite_eq_left hd, realWeight_one X s r hd]
    simp [hd, cofactorWindow, FiniteSieveWindow.primeWindow, Finset.sum_boole]
  · rw [ite_eq_right hd]
    have hz : ∀ k ∈ cofactorWindow r L R, ¬Nat.Prime (r.2.1*k) := by
      intro k hk hp
      exact hd ((completed_prime_iff r L R hi hL k hk).mp hp).1
    simp [Finset.sum_eq_zero (fun k hk => ite_eq_right (hz k hk))]

theorem window_count_split (X s L R : ℝ) (r : Representation)
    (hi : 0 < index r) (hL : (index r : ℝ) ≤ L) (hLR : L ≤ R) :
    realWeight X s r * ((⌊R/index r⌋₊ : ℝ)-(⌊L/index r⌋₊ : ℝ)) =
      (if r.2.1=1 then
        ((FiniteSieveWindow.primeWindow (L/index r) (R/index r)).card : ℝ) else 0) +
      realWeight X s r *
        ∑ k ∈ cofactorWindow r L R, if ¬Nat.Prime (r.2.1*k) then (1 : ℝ) else 0 := by
  have hip : (0 : ℝ) < index r := by exact_mod_cast hi
  have hf := Nat.floor_mono (div_le_div_of_nonneg_right hLR hip.le)
  have hc : ((⌊R/index r⌋₊ : ℝ)-(⌊L/index r⌋₊ : ℝ)) =
      ∑ _k ∈ cofactorWindow r L R, (1 : ℝ) := by
    simp [cofactorWindow, FiniteSieveWindow.window, Nat.card_Ioc, Nat.cast_sub hf]
  have hsplit : (∑ k ∈ cofactorWindow r L R, (1 : ℝ)) =
      (∑ k ∈ cofactorWindow r L R, if Nat.Prime (r.2.1*k) then (1 : ℝ) else 0) +
      (∑ k ∈ cofactorWindow r L R, if ¬Nat.Prime (r.2.1*k) then (1 : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hp : Nat.Prime (r.2.1*k) <;> simp [hp]
  rw [hc, hsplit, mul_add, prime_window_sum X s L R r hi hL]

theorem remainder_eq_prime_add_composite (X s L R : ℝ)
    (hi : ∀ r ∈ separatedSource X s, 0 < index r)
    (hL : ∀ r ∈ separatedSource X s, (index r : ℝ) ≤ L) (hLR : L ≤ R) :
    separatedRemainder X s L R = primeCofactorCount X s L R +
      compositeCofactorCount X s L R - (R-L)*sourceMass X s := by
  unfold separatedRemainder primeCofactorCount compositeCofactorCount sourceMass
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Finset.sum_filter, ← Finset.sum_add_distrib,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hh := window_count_split X s L R r (hi r hr) (hL r hr) hLR
  change realWeight X s r * floorKernel L R (index r) = _
  unfold floorKernel
  rw [mul_sub, hh]
  simp_rw [Finset.mul_sum]
  ring

theorem primeCofactorCount_nonneg (X s L R : ℝ) : 0 ≤ primeCofactorCount X s L R := by
  exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem eventually_moving_identity (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      ∀ Y : ℝ, 0 ≤ Y → Y ≤ X/2 → ∀ x ∈ Icc X (2*X),
        separatedRemainder X s (x-x*(Y/X)) x =
          primeCofactorCount X s (x-x*(Y/X)) x +
          compositeCofactorCount X s (x-x*(Y/X)) x -
          (x*(Y/X))*sourceMass X s := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 229/1000)).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000 : ℝ))
  filter_upwards [hpow, hlog, eventually_gt_atTop (1 : ℝ)] with X hp hlogX hX
  refine ⟨hX, hlogX, ?_⟩
  intro Y hY hYX x hx
  have hXp : 0 < X := by linarith
  have hxp : 0 ≤ x := by linarith [hx.1]
  have hrat : 0 ≤ Y/X := div_nonneg hY hXp.le
  have hrat2 : Y/X ≤ 1/2 := (div_le_iff₀ hXp).mpr (by linarith)
  have hL : X/2 ≤ x-x*(Y/X) := by
    have hh := mul_le_mul_of_nonneg_left hrat2 hxp
    linarith [hx.1]
  have hhalf : X^(771/1000 : ℝ) ≤ X/2 := by
    have hh := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hXp.le (771/1000 : ℝ))
    rw [← Real.rpow_add hXp] at hh
    norm_num at hh
    linarith
  have hgeom (r : Representation) (hr : r ∈ separatedSource X s) :=
    LongPairSeparatedCoreWork.support_geometry X s hX hs hs1 hlogX (index r)
      (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  have hi : ∀ r ∈ separatedSource X s, 0 < index r := by
    intro r hr
    have hh := (Real.rpow_pos_of_pos hXp (26/35 : ℝ)).trans (hgeom r hr).1
    exact_mod_cast hh
  have hil : ∀ r ∈ separatedSource X s, (index r : ℝ) ≤ x-x*(Y/X) := by
    intro r hr
    apply (hgeom r hr).2.le.trans
    apply le_trans (Real.rpow_le_rpow_of_exponent_le hX.le
      (show (771/1000 : ℝ)*(1-3*s) ≤ 771/1000 by linarith))
    exact hhalf.trans hL
  have hh := remainder_eq_prime_add_composite X s (x-x*(Y/X)) x hi hil
    (by nlinarith [mul_nonneg hxp hrat])
  convert hh using 1
  ring

theorem prime_term_shape (X s L R : ℝ) (hX : 1 < X) (hs : 0 < s)
    (hs1 : s ≤ 1/1000) (hlog : 1000 ≤ Real.log X)
    (r : Representation) (hr : r ∈ (separatedSource X s).filter (fun r => r.2.1=1))
    (hL : 0 ≤ L) (hLR : L ≤ R) (k : ℕ)
    (hk : k ∈ FiniteSieveWindow.primeWindow (L/index r) (R/index r)) :
    ∃ a b : ℕ, r.2.2=[a,b] ∧ r.1.Prime ∧ a.Prime ∧ b.Prime ∧ k.Prime ∧
      a≠b ∧ a<r.1 ∧ b<r.1 ∧
      L < ((r.1*a*b*k : ℕ) : ℝ) ∧ ((r.1*a*b*k : ℕ) : ℝ) ≤ R := by
  obtain ⟨hr, hd⟩ := Finset.mem_filter.mp hr
  obtain ⟨a,b,ht,hab,hap,hbp,hp,ha,hb,_⟩ :=
    LongPairSeparatedCoreWork.source_prime_shape X s hX hs hs1 hlog r hr
  have hie : index r = r.1*a*b := by simp [index, hd, ht, Nat.mul_assoc]
  have hi : (0 : ℝ) < index r := by rw [hie]; exact_mod_cast Nat.mul_pos (Nat.mul_pos hp.pos ha.pos) hb.pos
  obtain ⟨hkw, hkp⟩ := Finset.mem_filter.mp hk
  have hw := (SieveDivisorWindow.mem_window_iff (L/index r) (R/index r)
    (div_nonneg hL hi.le) (div_le_div_of_nonneg_right hLR hi.le) k).mp hkw
  refine ⟨a,b,ht,hp,ha,hb,hkp,hab,hap,hbp,?_,?_⟩
  · have hh := (div_lt_iff₀ hi).mp hw.1
    simpa only [hie, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hh
  · have hh := (le_div_iff₀ hi).mp hw.2
    simpa only [hie, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hh

/-- Every actual four-prime term has enough length for the new local
four-eighth-moment estimate, including the factor-of-two dyadic loss. -/
theorem eventually_prime_factor_lengths (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ 1000 ≤ Real.log X ∧
      ∀ Y : ℝ, 0 ≤ Y → Y ≤ X/2 → ∀ x ∈ Icc X (2*X),
        ∀ r ∈ (separatedSource X s).filter (fun r => r.2.1=1),
          ∀ k ∈ FiniteSieveWindow.primeWindow ((x-x*(Y/X))/index r) (x/index r),
            ∃ a b : ℕ, r.2.2=[a,b] ∧
              2*X^(57/250 : ℝ) ≤ (r.1 : ℝ) ∧
              2*X^(57/250 : ℝ) ≤ (a : ℝ) ∧
              2*X^(57/250 : ℝ) ≤ (b : ℝ) ∧
              2*X^(57/250 : ℝ) < (k : ℝ) := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/1000)).eventually
    (eventually_ge_atTop (4 : ℝ))
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000 : ℝ))
  filter_upwards [hpow, hlog, eventually_gt_atTop (1 : ℝ)] with X hpowX hlogX hX
  refine ⟨hX, hlogX, ?_⟩
  intro Y hY hYX x hx r hr k hk
  have hXp : 0 < X := by linarith
  have hxp : 0 ≤ x := by linarith [hx.1]
  have hrat : Y/X ≤ 1/2 := (div_le_iff₀ hXp).mpr (by linarith)
  have hL : X/2 ≤ x-x*(Y/X) := by
    have hh := mul_le_mul_of_nonneg_left hrat hxp
    linarith [hx.1]
  have hrs := (Finset.mem_filter.mp hr).1
  obtain ⟨a,b,ht,_,_,_,_,_,_,_⟩ :=
    LongPairSeparatedCoreWork.source_prime_shape X s hX hs hs1 hlogX r hrs
  have hfac := LongPairSeparatedCoreWork.source_factor_ranges X s hX hs hs1 hlogX r hrs
  have hbase : 2*X^(57/250 : ℝ) ≤ X^(229/1000 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ X^(1/1000 : ℝ) by linarith)
      (Real.rpow_nonneg hXp.le (57/250 : ℝ))
    rw [← Real.rpow_add hXp] at hh
    norm_num at hh
    exact hh
  have hp : 2*X^(57/250 : ℝ) ≤ (r.1 : ℝ) := hbase.trans
    ((Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (229/1000 : ℝ) ≤ 9/35)).trans hfac.1)
  have ha := (hfac.2.2 a (by simp [ht])).2.1
  have hb := (hfac.2.2 b (by simp [ht])).2.1
  refine ⟨a,b,ht,hp,hbase.trans ha.le,hbase.trans hb.le,?_⟩
  have hg := LongPairSeparatedCoreWork.support_geometry X s hX hs hs1 hlogX (index r)
    (Finset.mem_image.mpr ⟨r,hrs,rfl⟩)
  have hi : (0 : ℝ) < index r := (Real.rpow_pos_of_pos hXp _).trans hg.1
  have himax : (index r : ℝ) ≤ X^(771/1000 : ℝ) := hg.2.le.trans
    (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith))
  have hsmall : 4*X^(999/1000 : ℝ) ≤ X := by
    have hh := mul_le_mul_of_nonneg_right hpowX (Real.rpow_nonneg hXp.le (999/1000 : ℝ))
    rw [← Real.rpow_add hXp] at hh
    norm_num at hh
    exact hh
  have hprod : (2*X^(57/250 : ℝ))*(index r : ℝ) ≤ X/2 := by
    have hh := mul_le_mul_of_nonneg_left himax (show 0 ≤ 2*X^(57/250 : ℝ) by positivity)
    have he : 2*X^(57/250 : ℝ)*X^(771/1000 : ℝ) = 2*X^(999/1000 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hXp]
      norm_num
    rw [he] at hh
    linarith
  have hkw := (Finset.mem_filter.mp hk).1
  have hlow : (x-x*(Y/X))/index r < (k : ℝ) := by
    exact (Nat.floor_lt (div_nonneg (by linarith : 0 ≤ x-x*(Y/X)) hi.le)).mp
      (Finset.mem_Ioc.mp hkw).1
  have hmul := (div_lt_iff₀ hi).mp hlow
  nlinarith

#print axioms eventually_prime_factor_lengths
#print axioms eventually_moving_identity
run_cmd do
  for decl in [``realWeight_one, ``window_cofactor_one_lt, ``completed_prime_iff,
      ``prime_window_sum, ``window_count_split, ``remainder_eq_prime_add_composite,
      ``primeCofactorCount_nonneg, ``eventually_moving_identity,
      ``prime_term_shape, ``eventually_prime_factor_lengths] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "LITERAL SEPARATED CORE COFACTOR SPLIT PASSED"
end LongPairCofactorSwitchWork
