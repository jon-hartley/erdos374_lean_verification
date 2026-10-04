import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! Exact integer arithmetic for the finite Rosser profile certificate.
No floating evaluator, native decision procedure, or arithmetic hypothesis is
used to check the certificate. The prime-transfer interpretation is separate. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ProfileCertificateArithmetic

def scale : ℕ := 1000000000
def denominator (i k : ℕ) : ℕ := (i+10)*k+50*i+250
def roundedInverse (i k : ℕ) : ℕ :=
  (scale+denominator i k-1)/denominator i k
def outerCount (i j : ℕ) : ℕ := (50*(j+11-i)+(i+10)-1)/(i+10)
def forcingCount (i : ℕ) : ℕ := (50*(10-i)+(i+10)-1)/(i+10)

def prefixCheck (i : ℕ) : ℕ → List ℕ → Bool
  | _, [] => false
  | _, [_] => true
  | k, a::b::rest => decide (b=a+roundedInverse i k) && prefixCheck i (k+1) (b::rest)

def cumulativeNumerator (i j : ℕ) (p : List ℕ) : ℤ :=
  let k := outerCount i j
  let a := min k (forcingCount i)
  ((j+1)*p[a]!+(j+16)*(p[k]!-p[a]!) : ℕ) - ((k-a)*(scale/50) : ℕ)

def forcingNumerator (i : ℕ) (p : List ℕ) : ℤ :=
  (15*p[forcingCount i]! : ℕ) - (forcingCount i*(scale/50) : ℕ)

def cumulativeCheck (i : ℕ) (p : List ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | j, a::rest => decide ((a : ℤ)=cumulativeNumerator i j p) &&
      cumulativeCheck i p (j+1) rest

def decreasing : List ℕ → Bool
  | [] => true
  | [_] => true
  | a::b::rest => decide (b≤a) && decreasing (b::rest)

def increasing : List ℕ → Bool
  | [] => true
  | [_] => true
  | a::b::rest => decide (a≤b) && increasing (b::rest)

def weightedDifferences : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | _, [] => 0
  | a::_, [b] => a*b
  | a::rest, b::c::tail => a*(b-c)+weightedDifferences rest (c::tail)

def transitionCheck (prior : List ℕ) : List (List ℕ) → List ℕ → List ℕ → Bool
  | [], [], [] => true
  | row::rows, f::fs, v::vs =>
      decide (scale*f + scale*(scale/10000) + weightedDifferences row prior ≤ scale*v) &&
      transitionCheck prior rows fs vs
  | _, _, _ => false

def seedCheck : ℕ → List ℕ → Bool
  | _, [] => true
  | i, a::rest => decide (scale*4095*5^i ≤ a*331*6^i) && seedCheck (i+1) rest

theorem denominator_pos (i k : ℕ) : 0 < denominator i k := by
  unfold denominator
  omega

theorem roundedInverse_bound (i k : ℕ) :
    scale ≤ roundedInverse i k * denominator i k := by
  have hd := denominator_pos i k
  have h := Nat.mod_lt (scale+denominator i k-1) hd
  have he := Nat.mod_add_div (scale+denominator i k-1) (denominator i k)
  rw [Nat.mul_comm (denominator i k)] at he
  unfold roundedInverse
  omega

theorem roundedInverse_real_bound (i k : ℕ) :
    (1 : ℝ)/(denominator i k : ℝ) ≤ (roundedInverse i k : ℝ)/(scale : ℝ) := by
  have hd : (0 : ℝ) < denominator i k := by exact_mod_cast denominator_pos i k
  have hs : (0 : ℝ) < scale := by norm_num [scale]
  apply (div_le_div_iff₀ hd hs).mpr
  simpa only [one_mul, Nat.cast_mul] using
    (show (scale : ℝ) ≤ ((roundedInverse i k * denominator i k : ℕ) : ℝ) by
      exact_mod_cast roundedInverse_bound i k)

run_cmd do
  for decl in [``denominator_pos, ``roundedInverse_bound, ``roundedInverse_real_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "RATIONAL PROFILE INTEGER CHECKER: STANDARD AXIOMS ONLY"

end ProfileCertificateArithmetic
