import Item1SafeZetaCutoff
import Item1DyadicPhaseReduction
import PrimeNumberTheoremAnd.ZetaBounds

/-! Euler continuation and finite-prefix specialization using the retained
ZetaBounds declarations. The final theorem remains conditional on the
unproved analytic premise IntermediateDyadicPhaseAt. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators
namespace Item1PhaseZetaGrowth
open Item1DyadicPhaseReduction Item1SafeZetaCutoff Item1WeakCubicBudget

def line (sigma t : ℝ) : ℂ := (sigma:ℂ)+(t:ℂ)*Complex.I

def inversePrefix (Q : ℕ) (sigma t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range Q, 1/(n:ℂ)^line sigma t

def remainder (Q : ℕ) (sigma t : ℝ) : ℂ :=
  line sigma t * ∫ x in Ioi (Q:ℝ),
    (((Int.floor x:ℤ):ℂ)+1/2-(x:ℂ))/(x:ℂ)^(line sigma t+1)

/-- The original full improper remainder is retained; Qth endpoint also paid. -/
theorem euler_prefix_error (Q : ℕ) (sigma t : ℝ) (hQ : 1≤Q)
    (hs : 0<sigma) (hs2 : sigma≤2) (ht : 2≤t) :
    ‖riemannZeta (line sigma t)-inversePrefix Q sigma t‖ ≤
      (Q:ℝ)^(1-sigma)/t+(3/2)*(Q:ℝ)^(-sigma)+
        2*t*(Q:ℝ)^(-sigma)/sigma := by
  have hQn : 0<Q := by omega
  have hQp : (0:ℝ)<Q := by exact_mod_cast hQn
  have htp : 0<t := by linarith
  have hsne : line sigma t≠1 := by
    intro he
    have hi := congrArg Complex.im he
    simp [line] at hi
    linarith
  have hz := Zeta0EqZeta hQn (s := line sigma t) (by simpa [line] using hs) hsne
  have hid : riemannZeta (line sigma t)-inversePrefix Q sigma t =
      (1/(Q:ℂ)^line sigma t)+
      (-(Q:ℂ)^(1-line sigma t))/(1-line sigma t)+
      (-(Q:ℂ)^(-line sigma t))/2+remainder Q sigma t := by
    rw [←hz]
    unfold riemannZeta0 inversePrefix remainder
    rw [Finset.sum_range_succ]
    ring
  have hp : ‖1/(Q:ℂ)^line sigma t‖=(Q:ℝ)^(-sigma) := by
    rw [norm_div,norm_one,Complex.norm_natCast_cpow_of_pos hQn]
    simp only [line,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    rw [Real.rpow_neg hQp.le]
    simp only [one_div]
  have hhalf : ‖(-(Q:ℂ)^(-line sigma t))/2‖=(Q:ℝ)^(-sigma)/2 := by
    rw [norm_div,norm_neg,Complex.norm_natCast_cpow_of_pos hQn]
    norm_num [line]
  have hden : t≤‖1-line sigma t‖ := by
    simpa [line,abs_of_pos htp] using Complex.abs_im_le_norm (1-line sigma t)
  have hpol : ‖(-(Q:ℂ)^(1-line sigma t))/(1-line sigma t)‖≤
      (Q:ℝ)^(1-sigma)/t := by
    rw [norm_div,norm_neg,Complex.norm_natCast_cpow_of_pos hQn]
    have hnon : 0≤(Q:ℝ)^(1-sigma) := Real.rpow_nonneg hQp.le _
    simpa only [line,Complex.sub_re,Complex.one_re,Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
      sub_zero,add_zero] using div_le_div_of_nonneg_left hnon htp hden
  have hr : ‖remainder Q sigma t‖≤2*t*(Q:ℝ)^(-sigma)/sigma := by
    have hh := ZetaBnd_aux1 Q hQ (σ:=sigma) (t:=t) ⟨hs,hs2⟩
      (by rw [abs_of_pos htp]; exact ht)
    simpa only [remainder,line,abs_of_pos htp] using hh
  rw [hid]
  calc
    _ ≤ ‖1/(Q:ℂ)^line sigma t‖+
        ‖(-(Q:ℂ)^(1-line sigma t))/(1-line sigma t)‖+
        ‖(-(Q:ℂ)^(-line sigma t))/2‖+‖remainder Q sigma t‖ := by
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (Q:ℝ)^(-sigma)+(Q:ℝ)^(1-sigma)/t+(Q:ℝ)^(-sigma)/2+
        2*t*(Q:ℝ)^(-sigma)/sigma := by rw [hp,hhalf]; gcongr
    _ = _ := by ring

/-- Equality at n=0 is handled separately; no use of log 0 as a positive log. -/
theorem term_eq_inverse_cpow (n : ℕ) (sigma t : ℝ) (hs : 0<sigma) :
    term sigma t n=1/(n:ℂ)^line sigma t := by
  by_cases hn : n=0
  · subst n
    have hsne : line sigma t≠0 := by
      intro he
      have hh := congrArg Complex.re he
      simp [line] at hh
      linarith
    simp [term,Complex.zero_cpow hsne]
  · have hnp : 0<n := Nat.pos_of_ne_zero hn
    have hnr : (0:ℝ)<n := by exact_mod_cast hnp
    have hnC : (n:ℂ)≠0 := by exact_mod_cast hn
    have hlog : Complex.log (n:ℂ)=(Real.log (n:ℝ):ℂ) := by
      simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hnr.le).symm
    rw [term,ite_eq_right hn,Complex.ofReal_cpow hnr.le,one_div,←Complex.cpow_neg]
    simp only [Complex.ofReal_natCast,Complex.cpow_def_of_ne_zero hnC,hlog]
    rw [←Complex.exp_add]
    congr 1
    simp only [line]
    push_cast
    ring

/-- A conditional genuine zeta bound, not just a bound for a surrogate prefix. -/
theorem zeta_growth_from_intermediate_phase (sigma t : ℝ)
    (ht : 2≤t) (hL : 8≤Real.log t)
    (hstrip : 1-1/(Real.log t)^(2/3:ℝ)≤sigma) (hs1 : sigma≤1)
    (hphase : IntermediateDyadicPhaseAt t) :
    ‖riemannZeta (line sigma t)‖≤128*(Real.log t)^7 := by
  let J := cutoffIndex t
  let Q : ℕ := 2^J
  have hs : 3/4≤sigma := strip_sigma_lower (Real.log t) sigma hL hstrip
  obtain ⟨hQlo,hQhi,hJ⟩ := cutoff_bounds t (by linarith) (by linarith)
  have hQpos : 1≤Q := by
    dsimp [Q]
    have hh : 0<(2:ℕ)^J := pow_pos (by norm_num) J
    omega
  have hpre := dyadic_prefix_from_short_phase t sigma J (by linarith) hL hs hs1
    hstrip hJ (fun j hj => block_below_square t (by linarith) (by linarith) j hj) hphase
  have hid : (∑ n ∈ Finset.range Q,term sigma t n)=inversePrefix Q sigma t := by
    apply Finset.sum_congr rfl
    intro n _
    exact term_eq_inverse_cpow n sigma t (by linarith)
  change ‖∑ n ∈ Finset.range Q,term sigma t n‖≤_ at hpre
  rw [hid] at hpre
  have hpow := cutoff_powers Q t sigma ht hQlo hQhi hs hs1
  have herr := euler_prefix_error Q sigma t hQpos (by linarith) (by linarith) ht
  have hnum := euler_tail_budget t sigma ((Q:ℝ)^(1-sigma)) ((Q:ℝ)^(-sigma))
    (by linarith) (by linarith) hpow.1 (Real.rpow_nonneg (Nat.cast_nonneg Q) _) hpow.2
  have herror : ‖riemannZeta (line sigma t)-inversePrefix Q sigma t‖≤8 := herr.trans hnum
  have hZ : ‖riemannZeta (line sigma t)‖≤‖inversePrefix Q sigma t‖+8 := by
    have hh := norm_add_le (riemannZeta (line sigma t)-inversePrefix Q sigma t)
      (inversePrefix Q sigma t)
    rw [sub_add_cancel] at hh
    linarith
  exact final_growth_budget _ _ _ (by linarith) hZ hpre

end Item1PhaseZetaGrowth

#print axioms Item1PhaseZetaGrowth.euler_prefix_error
#print axioms Item1PhaseZetaGrowth.term_eq_inverse_cpow
#print axioms Item1PhaseZetaGrowth.zeta_growth_from_intermediate_phase

run_cmd do
  for target in [``Item1PhaseZetaGrowth.euler_prefix_error,
    ``Item1PhaseZetaGrowth.term_eq_inverse_cpow,
    ``Item1PhaseZetaGrowth.zeta_growth_from_intermediate_phase] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
