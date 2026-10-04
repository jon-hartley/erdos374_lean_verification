import OuterSmoothCoreWork

/-! Exact frequency bookkeeping for the nine source cuts. This is an
algebraic separation theorem, not a Fourier inversion or mean estimate. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace OuterMaskFrequencyWork
open OuterSmoothStepWork OuterBufferedSourceWork OuterSourceReindexWork
open SieveGeometricGrid

def primeSlope : Fin 9 → ℝ := ![-1,1,-1,1,1,-1,1,-1,1]
def divisorSlope : Fin 9 → ℝ := ![0,0,0,0,0,0,0,0,1]
def firstSlope (s : ℝ) (i : ℕ) : Fin 9 → ℝ :=
  ![-3,1/s^2,0,0,1/exponent s i,-1/exponent s (i+1),0,0,1]
def secondSlope (s : ℝ) (j : ℕ) : Fin 9 → ℝ :=
  ![0,0,-3,1/s^2,0,0,1/exponent s j,-1/exponent s (j+1),1]
def constantSlope (s : ℝ) : Fin 9 → ℝ :=
  ![1-3*s,-(1-3*s),1-3*s,-(1-3*s),-(1-3*s),1-3*s,
    -(1-3*s),1-3*s,-26/35]

def shift (ω c : Fin 9 → ℝ) : ℝ := ∑ n, ω n*c n

theorem gap_affine (X s : ℝ) (u : Slice) (i j p : ℕ) (n : Fin 9) :
    signedGap (Real.log (p:ℝ)) (cutoffLogs X s u i j) n =
      constantSlope s n*Real.log X + primeSlope n*Real.log (p:ℝ) +
      divisorSlope n*Real.log (u.1:ℝ) + firstSlope s i n*Real.log (u.2.1:ℝ) +
      secondSlope s j n*Real.log (u.2.2:ℝ) := by
  fin_cases n <;> simp [signedGap,cutoffLogs,constantSlope,primeSlope,
    divisorSlope,firstSlope,secondSlope,div_eq_mul_inv] <;> ring

theorem weighted_gap_affine (X s : ℝ) (u : Slice) (i j p : ℕ) (ω : Fin 9 → ℝ) :
    (∑ n, ω n*signedGap (Real.log (p:ℝ)) (cutoffLogs X s u i j) n) =
      shift ω (constantSlope s)*Real.log X + shift ω primeSlope*Real.log (p:ℝ) +
      shift ω divisorSlope*Real.log (u.1:ℝ) +
      shift ω (firstSlope s i)*Real.log (u.2.1:ℝ) +
      shift ω (secondSlope s j)*Real.log (u.2.2:ℝ) := by
  simp only [gap_affine,mul_add,Finset.sum_add_distrib,shift,Finset.sum_mul,mul_assoc]

def phase (t x : ℝ) : ℂ := Complex.exp (Complex.I * (t*x:ℝ))

theorem phase_add (a b x : ℝ) : phase (a+b) x = phase a x*phase b x := by
  simp [phase,add_mul,Complex.exp_add,mul_add]

theorem phase_norm (t x : ℝ) : ‖phase t x‖=1 := by
  simp [phase,Complex.norm_exp]

theorem phase_sum (ω x : Fin 9 → ℝ) :
    (∏n,phase (ω n) (x n)) = phase 1 (∑n,ω n*x n) := by
  simp only [phase,one_mul]
  rw [← Complex.exp_sum]
  congr 1
  simp [Finset.mul_sum]

theorem source_phase_factorization (X s : ℝ) (u : Slice) (i j p : ℕ)
    (ω : Fin 9 → ℝ) :
    (∏n,phase (ω n) (signedGap (Real.log (p:ℝ)) (cutoffLogs X s u i j) n)) =
      phase (shift ω (constantSlope s)) (Real.log X) *
      phase (shift ω primeSlope) (Real.log (p:ℝ)) *
      phase (shift ω divisorSlope) (Real.log (u.1:ℝ)) *
      phase (shift ω (firstSlope s i)) (Real.log (u.2.1:ℝ)) *
      phase (shift ω (secondSlope s j)) (Real.log (u.2.2:ℝ)) := by
  rw [phase_sum,weighted_gap_affine]
  simp [phase,Complex.exp_add,mul_add]

run_cmd do
  for decl in [``gap_affine, ``weighted_gap_affine, ``phase_add, ``phase_norm,
      ``phase_sum, ``source_phase_factorization] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterMaskFrequencyWork
