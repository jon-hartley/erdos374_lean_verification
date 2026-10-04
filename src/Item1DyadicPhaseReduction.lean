import Item1LongLogPhase
import Item1WeakCubicBudget

/-! Conditional finite-sum reduction.
IntermediateDyadicPhaseAt is the missing analytic assertion, not an axiom or a theorem.
The constructed conclusion is a finite Dirichlet prefix. The Euler continuation
is supplied separately by Item1PhaseZetaGrowth. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
open scoped BigOperators
namespace Item1DyadicPhaseReduction
open Item1FiniteAbelPhase Item1LongLogPhase Item1WeakCubicBudget

/-- Only INTERMEDIATE dyadic blocks and all their prefixes. UNPROVED.
Very short blocks are treated by the triangle inequality; M >= t is treated
by the retained first-derivative theorem. -/
def IntermediateDyadicPhaseAt (t : ℝ) : Prop :=
  ∀ j : ℕ, 1≤j → ((2^j:ℕ):ℝ)<t →
    6*(Real.log t)^(2/3:ℝ)*Real.log (Real.log t)<Real.log ((2^j:ℕ):ℝ) →
    ∀ K : ℕ, K≤2^j →
    ‖«prefix» (atom (2^j) t) K‖ ≤
      16*((2^j:ℕ):ℝ)*Real.exp
        (-((Real.log ((2^j:ℕ):ℝ))^3 /
          (200*(Real.log t)^2*(Real.log (Real.log t))^2)))

/-- Coefficients match n^(-sigma-it) for positive n; zero is separated. -/
def term (sigma t : ℝ) (n : ℕ) : ℂ :=
  if n=0 then 0 else ((n:ℝ)^(-sigma):ℝ) *
    Complex.exp (((-t*Real.log (n:ℝ):ℝ):ℂ)*Complex.I)

theorem block_identity (M K : ℕ) (sigma t : ℝ) (hM : 1≤M) :
    (∑ n ∈ Finset.range K, term sigma t (M+n)) =
      ∑ n ∈ Finset.range K, ((((M:ℝ)+n)^(-sigma):ℝ):ℂ)*atom M t n := by
  apply Finset.sum_congr rfl
  intro n _
  have hn : M+n≠0 := by omega
  simp only [term, hn, ite_false, atom, Nat.cast_add]

/-- Pointwise-in-height conditional bound; no eventual quantifier is moved. -/
theorem short_weighted_bound (M K : ℕ) (t sigma L : ℝ)
    (hM : 1≤M) (hK : K≤M) (hL : 1<L)
    (hs : 0≤sigma) (hstrip : 1-1/L^(2/3:ℝ)≤sigma)
    (hphase : ∀ k≤K, ‖«prefix» (atom M t) k‖ ≤
      16*(M:ℝ)*Real.exp (-(Real.log (M:ℝ))^3 /
        (200*L^2*(Real.log L)^2))) :
    ‖∑ n ∈ Finset.range K, term sigma t (M+n)‖≤16*L^6 := by
  have hMp : (0:ℝ)<M := by exact_mod_cast (by omega : 0<M)
  let u := Real.log (M:ℝ)
  let q := u^3/(200*L^2*(Real.log L)^2)
  have hu : 0≤u := Real.log_nonneg (by exact_mod_cast hM)
  have he := exponential_cubic_envelope L u (1-sigma) hL hu (by linarith)
  have hh := weighted_prefix_bound (atom M t)
    (fun n => ((M:ℝ)+n)^(-sigma)) K (16*(M:ℝ)*Real.exp (-q))
    (by positivity) (fun n => Real.rpow_nonneg (by positivity) _)
    (power_weights_antitone M sigma hM hs) (by
      intro k hk
      simpa only [u,q,neg_div] using hphase k hk)
  rw [block_identity M K sigma t hM]
  have hid : (16*(M:ℝ)*Real.exp (-q))*(M:ℝ)^(-sigma) =
      16*Real.exp ((1-sigma)*u-q) := by
    have hprod : (M:ℝ)*(M:ℝ)^(-sigma)=Real.exp ((1-sigma)*u) := by
      rw [Real.rpow_def_of_pos hMp]
      calc
        _ = Real.exp (Real.log (M:ℝ))*Real.exp (Real.log (M:ℝ)*(-sigma)) := by
          rw [Real.exp_log hMp]
        _ = _ := by rw [←Real.exp_add]; congr 1; dsimp [u]; ring
    calc
      _ = 16*((M:ℝ)*(M:ℝ)^(-sigma))*Real.exp (-q) := by ring
      _ = 16*Real.exp ((1-sigma)*u)*Real.exp (-q) := by rw [hprod]
      _ = _ := by rw [mul_assoc,←Real.exp_add]; congr 2 <;> ring
  have hh' : ‖∑ n ∈ Finset.range K,
      ((((M:ℝ)+n)^(-sigma):ℝ):ℂ)*atom M t n‖≤
      (16*(M:ℝ)*Real.exp (-q))*(M:ℝ)^(-sigma) := by simpa using hh
  rw [hid] at hh'
  exact hh'.trans (mul_le_mul_of_nonneg_left he (by norm_num))

/-- Exact unit norm of the log phase, with no frequency restriction. -/
theorem atom_norm (M n : ℕ) (t : ℝ) : ‖atom M t n‖=1 := by
  unfold atom
  exact Complex.norm_exp_ofReal_mul_I _

/-- The very short weighted blocks require only the triangle inequality. -/
theorem small_weighted_bound (M K : ℕ) (t sigma L : ℝ)
    (hM : 1≤M) (hK : K≤M) (hL : 1<L) (hs : 0≤sigma)
    (hstrip : 1-1/L^(2/3:ℝ)≤sigma)
    (hsmall : Real.log (M:ℝ)≤6*L^(2/3:ℝ)*Real.log L) :
    ‖∑ n ∈ Finset.range K, term sigma t (M+n)‖≤L^6 := by
  have hMp : (0:ℝ)<M := by exact_mod_cast (by omega : 0<M)
  have hLp : 0<L := by linarith
  have hpow : 0<L^(2/3:ℝ) := Real.rpow_pos_of_pos hLp _
  have hu : 0≤Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hpref (k : ℕ) (hk : k≤K) : ‖«prefix» (atom M t) k‖≤(M:ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.range k, ‖atom M t n‖ := norm_sum_le _ _
      _ = k := by simp only [atom_norm,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
      _ ≤ M := by exact_mod_cast hk.trans hK
  have hh := weighted_prefix_bound (atom M t)
    (fun n => ((M:ℝ)+n)^(-sigma)) K (M:ℝ) (by positivity)
    (fun n => Real.rpow_nonneg (by positivity) _)
    (power_weights_antitone M sigma hM hs) hpref
  have hmul : (M:ℝ)*(M:ℝ)^(-sigma)=
      Real.exp ((1-sigma)*Real.log (M:ℝ)) := by
    rw [Real.rpow_def_of_pos hMp]
    calc
      _ = Real.exp (Real.log (M:ℝ))*Real.exp (Real.log (M:ℝ)*(-sigma)) := by
        rw [Real.exp_log hMp]
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have hDu : (1-sigma)*Real.log (M:ℝ)≤Real.log (M:ℝ)/L^(2/3:ℝ) := by
    have hd : 1-sigma≤1/L^(2/3:ℝ) := by linarith
    have hm := mul_le_mul_of_nonneg_right hd hu
    calc
      _ ≤ (1/L^(2/3:ℝ))*Real.log (M:ℝ) := hm
      _ = _ := by ring
  have hu' : Real.log (M:ℝ)/L^(2/3:ℝ)≤6*Real.log L := by
    apply (div_le_iff₀ hpow).mpr
    nlinarith
  have he := Real.exp_le_exp.mpr (hDu.trans hu')
  have hexp : Real.exp (6*Real.log L)=L^6 := by
    rw [←show Real.log (L^6)=6*Real.log L by simpa using Real.log_pow L 6,
      Real.exp_log (pow_pos hLp 6)]
  rw [block_identity M K sigma t hM]
  have hh' : ‖∑ n ∈ Finset.range K,
      ((((M:ℝ)+n)^(-sigma):ℝ):ℂ)*atom M t n‖≤(M:ℝ)*(M:ℝ)^(-sigma) := by
    simpa using hh
  rw [hmul] at hh'
  exact hh'.trans (by simpa [hexp] using he)

/-- Long blocks need no IntermediateDyadicPhaseAt premise. -/
theorem long_weighted_constant (M K : ℕ) (t sigma : ℝ)
    (hM : 1≤M) (hK : K≤M) (ht : 1≤t) (htM : t≤M)
    (hMt : (M:ℝ)≤t^2) (hs0 : 1/2≤sigma) (hs1 : sigma≤1) :
    ‖∑ n ∈ Finset.range K, term sigma t (M+n)‖≤32 := by
  have htp : 0<t := by linarith
  have hMp : (0:ℝ)<M := by exact_mod_cast (by omega : 0<M)
  rw [block_identity M K sigma t hM]
  have hh := long_weighted_bound M K t sigma hM htp htM hK (by linarith)
  have hpow : (M:ℝ)^(1-sigma)≤t := by
    calc
      _ ≤ (M:ℝ)^(1/2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM) (by linarith)
      _ ≤ (t^2)^(1/2:ℝ) := Real.rpow_le_rpow hMp.le hMt (by norm_num)
      _ = t := by
        rw [←Real.rpow_natCast_mul htp.le 2 (1/2:ℝ)]
        norm_num
  have hid : (32*(M:ℝ)/t)*(M:ℝ)^(-sigma)=32*((M:ℝ)^(1-sigma)/t) := by
    rw [Real.rpow_sub hMp,Real.rpow_one,Real.rpow_neg hMp.le]
    ring
  rw [hid] at hh
  apply hh.trans
  have hd : (M:ℝ)^(1-sigma)/t≤1 := (div_le_one htp).mpr hpow
  nlinarith

/-- All finite blocks below a dyadic cutoff whose half is at most t^2.
The only non-scalar analytic premise is the explicitly unproved short-phase bound. -/
theorem dyadic_prefix_from_short_phase (t sigma : ℝ) (J : ℕ)
    (ht : 1≤t) (hL : 8≤Real.log t)
    (hs0 : 3/4≤sigma) (hs1 : sigma≤1)
    (hstrip : 1-1/(Real.log t)^(2/3:ℝ)≤sigma)
    (hcount : (J:ℝ)≤5*Real.log t)
    (hcut : ∀ j<J, ((2^j:ℕ):ℝ)≤t^2)
    (hphase : IntermediateDyadicPhaseAt t) :
    ‖∑ n ∈ Finset.range (2^J), term sigma t n‖≤80*(Real.log t)^7 := by
  rw [dyadic_partition]
  have hz : term sigma t 0=0 := by simp [term]
  rw [hz,zero_add]
  apply (norm_sum_le _ _).trans
  apply block_sum_budget _ _ _ (by linarith)
  · simpa using hcount
  · intro j hj
    have hjJ := Finset.mem_range.mp hj
    by_cases hj0 : j=0
    · subst j
      simp only [pow_zero,Finset.range_one,Finset.sum_singleton,Nat.add_zero]
      have hid : term sigma t 1=1 := by simp [term]
      rw [hid,norm_one]
      have hp : (1:ℝ)≤(Real.log t)^6 := one_le_pow₀ (by linarith)
      nlinarith
    · have hMj : 1≤(2:ℕ)^j := by
        have hh : 0<(2:ℕ)^j := pow_pos (by norm_num) j
        omega
      by_cases hsmall : ((2^j:ℕ):ℝ)<t
      · by_cases hvery : Real.log ((2^j:ℕ):ℝ)≤
            6*(Real.log t)^(2/3:ℝ)*Real.log (Real.log t)
        · have hh := small_weighted_bound (2^j) (2^j) t sigma (Real.log t)
            hMj le_rfl (by linarith) (by linarith) hstrip hvery
          have hp : 0≤(Real.log t)^6 := by positivity
          nlinarith
        · exact short_weighted_bound (2^j) (2^j) t sigma (Real.log t)
            hMj le_rfl (by linarith) (by linarith) hstrip
            (by simpa only [neg_div] using hphase j (by omega) hsmall (by linarith))
      · have hh := long_weighted_constant (2^j) (2^j) t sigma hMj le_rfl
          ht (by linarith) (hcut j hjJ) (by linarith) hs1
        have hp : (2:ℝ)≤(Real.log t)^6 := by
          have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8) hL 6
          norm_num at hp
          linarith
        nlinarith

end Item1DyadicPhaseReduction

run_cmd do
  for n in [``Item1DyadicPhaseReduction.block_identity,
    ``Item1DyadicPhaseReduction.short_weighted_bound,
    ``Item1DyadicPhaseReduction.atom_norm,
    ``Item1DyadicPhaseReduction.small_weighted_bound,
    ``Item1DyadicPhaseReduction.long_weighted_constant,
    ``Item1DyadicPhaseReduction.dyadic_prefix_from_short_phase] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"

#print axioms Item1DyadicPhaseReduction.dyadic_prefix_from_short_phase
