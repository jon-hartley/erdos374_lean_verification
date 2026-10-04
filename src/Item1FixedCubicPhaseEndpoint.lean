import Item1IntermediatePhaseGeometry
import Item1PhaseConstantAbsorption
import Item1IntermediatePhaseEndpoint

/-! A uniform fixed-constant cubic phase bound implies the original phase
premise and the literal Item 1 endpoint. The cubic bound remains a hypothesis.
The threshold is explicit and independent of the block and prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter MeasureTheory Set

namespace Item1FixedCubicPhaseEndpoint
open Item1FiniteAbelPhase Item1LongLogPhase Item1IntermediatePhaseEndpoint

/-- An unproved analytic input with arbitrary fixed positive constants.
It controls every prefix of every intermediate dyadic block. -/
def FixedCubicPhaseInput (C c T : ℝ) : Prop :=
  ∀ t : ℝ, T ≤ t → ∀ j : ℕ, 1 ≤ j → ((2^j:ℕ):ℝ) < t →
    6*(Real.log t)^(2/3:ℝ)*Real.log (Real.log t) < Real.log ((2^j:ℕ):ℝ) →
    ∀ K : ℕ, K ≤ 2^j →
      ‖«prefix» (atom (2^j) t) K‖ ≤
        C*((2^j:ℕ):ℝ)*Real.exp
          (-c*((Real.log ((2^j:ℕ):ℝ))^3/(Real.log t)^2))

def loglogThreshold (C c : ℝ) : ℝ := max 1 (max (1/c) (C/c))

def phaseThreshold (C c T : ℝ) : ℝ :=
  max T (Real.exp (Real.exp (loglogThreshold C c)))

/-- No optimization of C or c is needed. The threshold is chosen before t,j,K. -/
theorem intermediate_phase_of_fixed_cubic (C c T : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hinput : FixedCubicPhaseInput C c T) :
    IntermediatePhaseInput (phaseThreshold C c T) := by
  intro t ht j hj hMt hmid K hK
  let L := Real.log t
  let y := Real.log L
  let u := Real.log ((2^j:ℕ):ℝ)
  let q := u^3/L^2
  have htbig : Real.exp (Real.exp (loglogThreshold C c)) ≤ t :=
    (le_max_right T _).trans ht
  have htpos : 0 < t := (Real.exp_pos _).trans_le htbig
  have hL : Real.exp (loglogThreshold C c) ≤ L :=
    (Real.le_log_iff_exp_le htpos).mpr htbig
  have hLp : 0 < L := (Real.exp_pos _).trans_le hL
  have hy : loglogThreshold C c ≤ y :=
    (Real.le_log_iff_exp_le hLp).mpr hL
  have hB1 : 1 ≤ loglogThreshold C c := le_max_left _ _
  have hy1 : 1 ≤ y := hB1.trans hy
  have hL1 : 1 < L := by
    have hh := Real.add_one_le_exp (loglogThreshold C c)
    linarith only [hh,hB1,hL]
  have h1cy : 1/c ≤ y :=
    ((le_max_left (1/c) (C/c)).trans (le_max_right 1 _)).trans hy
  have hCcy : C/c ≤ y :=
    ((le_max_right (1/c) (C/c)).trans (le_max_right 1 _)).trans hy
  have hcy : 1 ≤ c*y := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp h1cy
  have hCy : C ≤ c*y := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hCcy
  have hgeom : 216*y^3 < q :=
    Item1IntermediatePhaseGeometry.intermediate_cubic_lower L u hL1 hmid
  have hycube : y ≤ y^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hy1 (by norm_num : 1 ≤ 3)
  have hq : 2*y ≤ q := by nlinarith only [hgeom,hycube,hy1]
  have hs := Item1PhaseConstantAbsorption.fixed_constant_absorption
    C c q y hC hc hy1 hcy hCy hq
  have hbound := hinput t ((le_max_left T _).trans ht) j hj hMt hmid K hK
  have hscaled := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ ((2^j:ℕ):ℝ) by positivity)
  have hid : q/(200*y^2) = u^3/(200*L^2*y^2) := by
    dsimp [q]
    ring
  rw [hid] at hscaled
  calc
    _ ≤ C*((2^j:ℕ):ℝ)*Real.exp (-c*q) := hbound
    _ ≤ 16*((2^j:ℕ):ℝ)*Real.exp (-(u^3/(200*L^2*y^2))) := by
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hscaled
    _ = _ := rfl

/-- The original physical source, half-width and logarithmic error are retained.
The sole analytic assumption is the displayed all-prefix cubic phase input. -/
theorem literal_item1_of_fixed_cubic (C c T : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hinput : FixedCubicPhaseInput C c T) :
    ∀ᶠ X : ℝ in atTop,
      (∫ x in Icc X (2*X), CancellationTransferCenter.sourceResidualAbs X x
        (x*(X^((101:ℝ)/1000)/2)/X))/X ≤ 1/(Real.log X)^2 := by
  exact literal_item1_of_intermediate_phase (phaseThreshold C c T)
    (intermediate_phase_of_fixed_cubic C c T hC hc hinput)

end Item1FixedCubicPhaseEndpoint

#print Item1FixedCubicPhaseEndpoint.FixedCubicPhaseInput
#check Item1FixedCubicPhaseEndpoint.literal_item1_of_fixed_cubic
run_cmd do
  for target in [``Item1FixedCubicPhaseEndpoint.intermediate_phase_of_fixed_cubic,
      ``Item1FixedCubicPhaseEndpoint.literal_item1_of_fixed_cubic] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1FixedCubicPhaseEndpoint: 2 theorem guards passed; cubic phase input remains unproved."
