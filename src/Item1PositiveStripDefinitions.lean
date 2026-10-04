import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! Exact original definitions, separated from the contour and Mellin proofs.
No estimate or nonvanishing statement is proved or assumed by this module. -/
set_option autoImplicit false
noncomputable section
namespace Item1RampDirichlet

def zetaLogDeriv (s : ℂ) : ℂ := -deriv riemannZeta s/riemannZeta s

end Item1RampDirichlet

namespace Item1ZetaContourGeometry
open Item1RampDirichlet

def PositiveStrip (a C T₀ : ℝ) : Prop :=
  ∀ σ y : ℝ, T₀ ≤ y → 1-a/(Real.log y)^(3/4:ℝ) ≤ σ → σ ≤ 2 →
    DifferentiableAt ℂ zetaLogDeriv ((σ:ℂ)+(y:ℂ)*Complex.I) ∧
    ‖zetaLogDeriv ((σ:ℂ)+(y:ℂ)*Complex.I)‖ ≤ C*(Real.log y)^9

end Item1ZetaContourGeometry
