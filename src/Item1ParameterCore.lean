import Item1VmvtNumericalEndpoint
import Mathlib.Algebra.Order.Floor.Ring

/-! Definitions for the proposed one-third parameter argument. This module
contains definitions only; it does not assert uniform phase cancellation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Item1ParameterCore

def gain (lam x : ℝ) : ℝ :=
  max 0 (min (x/3) (min (x-lam) (lam-x/3)))

def modelExponent (lam x : ℝ) : ℝ :=
  min (2*x/3) (max (x/3) (max (lam-x/3) (x-lam)))

def degree (lam : ℝ) : ℕ := Nat.ceil (3*lam) + 2

def momentOrder (d : ℕ) : ℕ := 4*d^2

def etaLoss (d : ℕ) : ℝ :=
  (d:ℝ)^2/3 * (1-1/(d:ℝ))^(4*d)

def totalGain (d : ℕ) (lam : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 d, gain lam (j:ℝ)

def logFactor (d j : ℕ) (m : ℝ) : ℝ :=
  1 + Real.log (8*(d:ℝ)^2) + (j:ℝ)*m

def factor (d j : ℕ) (m : ℝ) : ℝ :=
  1600*(d:ℝ)^4*(j:ℝ)*(2:ℝ)^j*logFactor d j m

def rawLoss (d : ℕ) (m : ℝ) : ℝ :=
  192*(d:ℝ)^3*Real.log (d:ℝ) +
  (d:ℝ)*Real.log 1600 + 5*(d:ℝ)*Real.log (d:ℝ) +
  (3/2:ℝ)*(d:ℝ)*((d:ℝ)+1)*Real.log 2 +
  (d:ℝ)*Real.log (1+Real.log (8*(d:ℝ)^2)+(d:ℝ)*m)

end Item1ParameterCore
