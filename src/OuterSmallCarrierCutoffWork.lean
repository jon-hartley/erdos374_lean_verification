import SmallWeightPrimeCutoffWork
import OuterPairBoxIntervalsWork

/-! The actual small-divisor carrier is downward stable in the outer prime.
This is about set membership as well as the previously proved weight value. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace OuterSmallCarrierCutoffWork
open SieveWeightedCutoffs

theorem selectedSupport_mono (T T' z z' : ℝ) (hT : T≤T') (hz : z≤z')
    (mode : Bool) :
    SieveSelectedWindow.support (SieveRosser.cubicGate T) mode 1 (SieveSmallWeights.primes z) ⊆
      SieveSelectedWindow.support (SieveRosser.cubicGate T') mode 1 (SieveSmallWeights.primes z') := by
  intro d hd
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hd
  exact Finset.mem_image.mpr ⟨f,SmallWeightPrimeCutoffWork.selected_mono T T' z z' hT hz mode hf,rfl⟩

theorem carrier_mono (T T' z z' : ℝ) (hT : T≤T') (hz : z≤z') :
    SieveVectorConvolution.carrier (SieveRosser.cubicGate T) 1 (SieveSmallWeights.primes z) ⊆
      SieveVectorConvolution.carrier (SieveRosser.cubicGate T') 1 (SieveSmallWeights.primes z') := by
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · exact Finset.mem_union.mpr (Or.inl (selectedSupport_mono T T' z z' hT hz false hd))
  · exact Finset.mem_union.mpr (Or.inr (selectedSupport_mono T T' z z' hT hz true hd))

theorem original_carrier_stable_downward (X s : ℝ) (hX : 0<X) (hs : 0≤s)
    (p q d : ℕ) (hp : 0<p) (hpq : p≤q)
    (hd : d∈SieveUpperBoxWindow.smallCarrier (level X s/q) s) :
    d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s := by
  have hq : 0<q := lt_of_lt_of_le hp hpq
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hpqR : (p:ℝ)≤q := by exact_mod_cast hpq
  have hnum : 0≤level X s := by unfold level; exact Real.rpow_nonneg hX.le _
  have hD : level X s/q≤level X s/p :=
    div_le_div_of_nonneg_left hnum hpR hpqR
  have hD0 : 0≤level X s/q := by
    exact div_nonneg hnum (by exact_mod_cast hq.le)
  have hT := Real.rpow_le_rpow hD0 hD hs
  have hz := Real.rpow_le_rpow hD0 hD (sq_nonneg s)
  exact carrier_mono _ _ _ _ hT hz hd

run_cmd do
  for decl in [``selectedSupport_mono, ``carrier_mono, ``original_carrier_stable_downward] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSmallCarrierCutoffWork
