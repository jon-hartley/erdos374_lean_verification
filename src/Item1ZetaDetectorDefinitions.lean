import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! The original translated-zeta and circle-growth definitions, factored out
without changing their names or bodies so independent growth estimates can
be checked before the zero-removal theorem. -/
set_option autoImplicit false
noncomputable section
open Set Metric Complex
namespace Item1AutomaticZetaDetector

def center (σ t : ℝ) : ℂ := (σ:ℂ)+(t:ℂ)*Complex.I
def shifted (σ t : ℝ) (z : ℂ) : ℂ := riemannZeta (center σ t+z)

/-- Relative growth on the original circle. Boundary zeros are permitted. -/
def DiskGrowth (σ t R M : ℝ) : Prop :=
  ∀ z ∈ sphere (0:ℂ) R,
    ‖shifted σ t z‖ ≤ Real.exp M * ‖shifted σ t 0‖

end Item1AutomaticZetaDetector
