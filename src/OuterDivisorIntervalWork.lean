import OuterPrimeIntervalRestrictionWork
import OuterSmallCarrierCutoffWork

/-! The entire small-divisor atom, including carrier membership, has an
interval cutoff depending only on the divisor and outer prime set.
Tuple primes and completed cofactors do not enter this cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable

namespace OuterDivisorIntervalWork
open LongerTupleActualProfiles SieveWeightedCutoffs

def divisorAtom (X s : ℝ) (d p : ℕ) : ℂ :=
  if d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s then
    originalWeight X s true (p,d,[]) else 0

theorem divisorAtom_norm_le (X s : ℝ) (d p : ℕ) : ‖divisorAtom X s d p‖≤1 := by
  unfold divisorAtom
  split_ifs
  · exact originalWeight_norm_le X s true _
  · simp

theorem divisorAtom_interval (X s : ℝ) (hX : 0<X) (hs : 0≤s)
    (P : Finset ℕ) (hP : ∀p∈P,0<p) (d : ℕ) :
    ∃lo hi : ℕ, ∃c : ℂ, ‖c‖≤1 ∧ ∀p∈P,
      divisorAtom X s d p = if lo≤p ∧ p≤hi then c else 0 := by
  let f := fun p => originalWeight X s true (p,d,[])
  have hweight : ∃lo hi : ℕ, ∃c : ℂ, ∀p∈P,
      f p = if lo≤p ∧ p≤hi then c else 0 := by
    obtain ⟨cut,_,_,hh⟩ := SmallWeightPrimeCutoffWork.originalWeight_interval
      X s hX hs 0 (P.sup id) d (Nat.zero_le _) []
    refine ⟨1,cut,originalWeight X s true (1,d,[]),?_⟩
    intro p hp
    have hp0 := hP p hp
    have hpI : p∈Finset.Ioc 0 (P.sup id) :=
      Finset.mem_Ioc.mpr ⟨hp0,Finset.le_sup (f:=id) hp⟩
    simpa only [Nat.zero_add,show 1≤p by omega,true_and] using hh p hpI
  simpa only [divisorAtom,f] using OuterPrimeIntervalRestrictionWork.restrict_weighted_interval P f
    (fun p => d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s)
    (fun _ _ q hq r _ _ hqr _ hr =>
      OuterSmallCarrierCutoffWork.original_carrier_stable_downward X s hX hs q r d
        (hP q hq) hqr hr)
    (fun p _ => originalWeight_norm_le X s true (p,d,[])) hweight

run_cmd do
  for decl in [``divisorAtom_norm_le, ``divisorAtom_interval] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterDivisorIntervalWork
