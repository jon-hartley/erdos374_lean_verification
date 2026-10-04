import OuterMaskFrequencyWork

/-! Exact separation of a single Fourier mode, including an independent
completed cofactor and the actual signed small-divisor atom. No inversion,
truncation estimate, or cancellation bound is asserted here. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace OuterSeparatedFourierModeWork
open OuterMaskFrequencyWork OuterSmoothStepWork OuterBufferedSourceWork
open OuterDivisorIntervalWork

def logPhase (t : ℝ) (n : ℕ) : ℂ := phase t (Real.log (n:ℝ))

theorem logPhase_add (t v : ℝ) (n : ℕ) :
    logPhase (t+v) n = logPhase t n*logPhase v n := phase_add _ _ _

theorem logPhase_norm (t : ℝ) (n : ℕ) : ‖logPhase t n‖=1 := phase_norm _ _

theorem logPhase_mul (t : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    logPhase t (m*n) = logPhase t m*logPhase t n := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [logPhase,phase,Nat.cast_mul,Real.log_mul hm' hn',mul_add,Complex.exp_add]

def sourceMode (X s : ℝ) (i j d p a b : ℕ) (ω : Fin 9 → ℝ) : ℂ :=
  ∏n,phase (ω n) (signedGap (Real.log (p:ℝ)) (cutoffLogs X s (d,a,b) i j) n)

theorem mode_with_base_frequency (X s t : ℝ) (i j d p a b k : ℕ)
    (ω : Fin 9 → ℝ) :
    sourceMode X s i j d p a b ω *
      (logPhase t p*logPhase t d*logPhase t a*logPhase t b*logPhase t k) =
      phase (shift ω (constantSlope s)) (Real.log X) *
      logPhase (t+shift ω divisorSlope) d *
      logPhase (t+shift ω primeSlope) p *
      logPhase (t+shift ω (firstSlope s i)) a *
      logPhase (t+shift ω (secondSlope s j)) b * logPhase t k := by
  rw [sourceMode,source_phase_factorization]
  simp only [logPhase,phase_add]
  ring

theorem mode_with_product_frequency (X s t : ℝ) (i j d p a b k : ℕ)
    (hd : 0 < d) (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (ω : Fin 9 → ℝ) :
    sourceMode X s i j d p a b ω * logPhase t (p*d*a*b*k) =
      phase (shift ω (constantSlope s)) (Real.log X) *
      logPhase (t+shift ω divisorSlope) d *
      logPhase (t+shift ω primeSlope) p *
      logPhase (t+shift ω (firstSlope s i)) a *
      logPhase (t+shift ω (secondSlope s j)) b * logPhase t k := by
  rw [logPhase_mul t _ k (by positivity) hk,
    logPhase_mul t _ b (by positivity) hb,
    logPhase_mul t _ a (by positivity) ha,logPhase_mul t p d hp hd]
  exact mode_with_base_frequency X s t i j d p a b k ω

/-- The tuple coefficient may retain the full tuple mask and arbitrary
pair coupling. The prime factor retains the actual signed divisor atom.
The cofactor coefficient has no separator-frequency shift. -/
theorem finite_mode_separation (X s t : ℝ) (i j d : ℕ) (ω : Fin 9 → ℝ)
    (P A B K : Finset ℕ) (q : ℕ → ℕ → ℂ) (c : ℕ → ℂ) :
    (∑p∈P, ∑a∈A, ∑b∈B, ∑k∈K,
      ((divisorAtom X s d p).re:ℂ)*q a b*c k*sourceMode X s i j d p a b ω *
        (logPhase t p*logPhase t d*logPhase t a*logPhase t b*logPhase t k)) =
      phase (shift ω (constantSlope s)) (Real.log X) *
      logPhase (t+shift ω divisorSlope) d *
      (∑p∈P, ((divisorAtom X s d p).re:ℂ)*logPhase (t+shift ω primeSlope) p) *
      (∑a∈A, ∑b∈B, q a b*logPhase (t+shift ω (firstSlope s i)) a*
        logPhase (t+shift ω (secondSlope s j)) b) *
      (∑k∈K, c k*logPhase t k) := by
  simp only [Finset.sum_mul,Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := B) (t := P),
    Finset.sum_comm (s := A) (t := P), Finset.sum_comm (s := K) (t := P),
    Finset.sum_comm (s := K) (t := A), Finset.sum_comm (s := K) (t := B)]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro k hk
  have hh := mode_with_base_frequency X s t i j d p a b k ω
  calc
    _ = (((divisorAtom X s d p).re:ℂ)*q a b*c k)*
        (sourceMode X s i j d p a b ω *
          (logPhase t p*logPhase t d*logPhase t a*logPhase t b*logPhase t k)) := by ring
    _ = _ := by rw [hh]; ring

run_cmd do
  for decl in [``logPhase_add, ``logPhase_norm, ``logPhase_mul,
      ``mode_with_base_frequency, ``mode_with_product_frequency, ``finite_mode_separation] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSeparatedFourierModeWork
