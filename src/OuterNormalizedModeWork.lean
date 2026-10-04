import OuterModeUnitCapWork
import MellinWindowFactor

/-! Exact normalized Dirichlet factorization of the completed source
mode. With the convention n^(-sigma-it), source phases shift t to
t-shift, and the flat cofactor frequency remains t. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace OuterNormalizedModeWork
open OuterModeUnitCapWork OuterSeparatedFourierModeWork OuterMaskFrequencyWork
open OuterDivisorIntervalWork Erdos374.HarmanGram152 MellinWindowFactor

theorem vertical_phase (n : ℕ) (hn : 0<n) (σ t : ℝ) :
    (n:ℂ)^(-line σ t) = (((n:ℝ)^σ:ℝ):ℂ)⁻¹*logPhase (-t) n := by
  unfold line
  rw [cpow_vertical_factor152 hn]
  congr 1
  unfold Erdos374.HarmanAnalytic151MeanSquare.exponentialKernel151 logPhase phase
  congr 1
  push_cast
  ring

theorem phase_shift (n : ℕ) (hn : 0<n) (σ t v : ℝ) :
    logPhase v n*(n:ℂ)^(-line σ t) = (n:ℂ)^(-line σ (t-v)) := by
  rw [vertical_phase n hn,vertical_phase n hn,
    show -(t-v)=v+(-t) by ring,logPhase_add]
  ring

theorem nat_mul_cpow (m n : ℕ) (z : ℂ) :
    ((m*n:ℕ):ℂ)^z=(m:ℂ)^z*(n:ℂ)^z := by
  simpa only [Complex.ofReal_natCast,Nat.cast_mul] using
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n) z

theorem normalized_source_term (X s σ t : ℝ) (i j d p a b k : ℕ)
    (hd : 0<d) (hp : 0<p) (ha : 0<a) (hb : 0<b) (_hk : 0<k)
    (ω : Fin 9→ℝ) :
    sourceMode X s i j d p a b ω*((p*d*a*b*k:ℕ):ℂ)^(-line σ t) =
      phase (shift ω (constantSlope s)) (Real.log X) *
      (d:ℂ)^(-line σ (t-shift ω divisorSlope)) *
      (p:ℂ)^(-line σ (t-shift ω primeSlope)) *
      (a:ℂ)^(-line σ (t-shift ω (firstSlope s i))) *
      (b:ℂ)^(-line σ (t-shift ω (secondSlope s j))) *
      (k:ℂ)^(-line σ t) := by
  simp only [nat_mul_cpow]
  rw [sourceMode,source_phase_factorization]
  rw [←phase_shift d hd,←phase_shift p hp,←phase_shift a ha,←phase_shift b hb]
  dsimp only [logPhase]
  ring

def sourcePolynomial (X s : ℝ) (i j d : ℕ) (ω : Fin 9→ℝ)
    (P A B K : Finset ℕ) (q : ℕ→ℕ→ℂ) (σ t : ℝ) : ℂ :=
  ∑p∈P,∑a∈A,∑b∈B,∑k∈K,
    ((divisorAtom X s d p).re:ℂ)*q a b*
      sourceMode X s i j d p a b ω*((p*d*a*b*k:ℕ):ℂ)^(-line σ t)

theorem sourcePolynomial_factorization (X s : ℝ) (i j d : ℕ) (ω : Fin 9→ℝ)
    (P A B K : Finset ℕ) (q : ℕ→ℕ→ℂ) (σ t : ℝ)
    (hd : 0<d) (hP : ∀p∈P,0<p) (hA : ∀a∈A,0<a)
    (hB : ∀b∈B,0<b) (hK : ∀k∈K,0<k) :
    sourcePolynomial X s i j d ω P A B K q σ t =
      phase (shift ω (constantSlope s)) (Real.log X) *
      (d:ℂ)^(-line σ (t-shift ω divisorSlope)) *
      remainingFactor X s i j d ω P A B q σ t *
      verticalDirichlet152 K (fun _ => 1) σ t := by
  unfold sourcePolynomial remainingFactor pairPolynomial verticalDirichlet152
  simp only [Finset.mul_sum,Finset.sum_mul,one_mul]
  simp_rw [Finset.sum_comm (s := B) (t := P),
    Finset.sum_comm (s := A) (t := P),Finset.sum_comm (s := K) (t := P),
    Finset.sum_comm (s := K) (t := A),Finset.sum_comm (s := K) (t := B)]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro k hk
  have hh := normalized_source_term X s σ t i j d p a b k
    hd (hP p hp) (hA a ha) (hB b hb) (hK k hk) ω
  calc
    _ = (((divisorAtom X s d p).re:ℂ)*q a b)*
      (sourceMode X s i j d p a b ω*((p*d*a*b*k:ℕ):ℂ)^(-line σ t)) := by ring
    _ = _ := by rw [hh]; dsimp only [line]; ring

run_cmd do
  for decl in [``vertical_phase, ``phase_shift, ``nat_mul_cpow,
      ``normalized_source_term, ``sourcePolynomial_factorization] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
end OuterNormalizedModeWork
