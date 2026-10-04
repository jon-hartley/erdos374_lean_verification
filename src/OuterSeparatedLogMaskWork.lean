import OuterPairLogConstraintsWork
import OuterDivisorIntervalWork

/-! Separate the actual fixed-box source into a small-divisor atom, a
tuple-only mask, and nine affine inequalities in logarithms. The completed
window adds two more affine inequalities. All identities are exact. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable

namespace OuterSeparatedLogMaskWork
open SieveGeometricGrid SieveWeightedCutoffs PositiveSharpBoxedCount
open LongerTupleEncoding LongerTupleActualProfiles
open OuterPairSourceIntervalWork OuterSeparatedCoreIntervalWork
open OuterPairLogConstraintsWork OuterCompletedIntervalWork OuterDivisorIntervalWork

def poolCuts (s H v w : ℝ) : Prop :=
  v+3*w < H ∧ s^2*H ≤ s^2*v+w

def boxCuts (s : ℝ) (i : ℕ) (H v w : ℝ) : Prop :=
  exponent s i*H ≤ exponent s i*v+w ∧
    exponent s (i+1)*v+w < exponent s (i+1)*H

def tupleMask (X s : ℝ) (a b i j : ℕ) : Prop :=
  a.Prime ∧ b.Prime ∧ j ≤ i ∧ 3*exponent s i<1 ∧
    LongerTupleSector.allLong X [a,b] ∧
    X^(229/1000:ℝ)<(b:ℝ) ∧ X^(229/1000:ℝ)<(a:ℝ) ∧
    a≠b ∧ X^(9/50:ℝ)<(Nat.dist a b:ℝ)

def logMask (X s : ℝ) (d a b i j p : ℕ) : Prop :=
  let H := (1-3*s)*Real.log X
  let v := Real.log (p:ℝ)
  let wa := Real.log (a:ℝ)
  let wb := Real.log (b:ℝ)
  poolCuts s H v wa ∧ poolCuts s H v wb ∧
    boxCuts s i H v wa ∧ boxCuts s j H v wb ∧
    (26/35:ℝ)*Real.log X < v+Real.log (d:ℝ)+wa+wb

def windowCuts (L R v vd wa wb vk : ℝ) : Prop :=
  Real.log L < v+vd+wa+wb+vk ∧ v+vd+wa+wb+vk ≤ Real.log R

theorem coreBoxSource_log_iff (X s : ℝ) (p d a b i j : ℕ)
    (hX : 1<X) (hp : 0<p) (hd : 0<d) (ha : 0<a) (hb : 0<b) :
    coreBoxSource X s d a b i j p ↔
      p∈largePrimes X ∧ d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s ∧
        tupleMask X s a b i j ∧ logMask X s d a b i j p := by
  have hX0 : 0<X := by linarith
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have hprod : (26/35:ℝ)*Real.log X <
      Real.log (p:ℝ)+Real.log (d:ℝ)+Real.log (a:ℝ)+Real.log (b:ℝ) →
      (109/200:ℝ)*Real.log X <
      Real.log (p:ℝ)+Real.log (d:ℝ)+Real.log (a:ℝ)+Real.log (b:ℝ) := by
    intro hh
    have := Real.log_pos hX
    linarith
  simp only [coreBoxSource,fixedBoxSource,coreRestrictions]
  rw [pool_log_iff X s p a hX0 hp ha,pool_log_iff X s p b hX0 hp hb,
    inBox_log_iff X s p a i hX0 hpR haR,inBox_log_iff X s p b j hX0 hpR hbR,
    product_lower_log_iff X (109/200) p d a b hX0 hp hd ha hb,
    product_lower_log_iff X (26/35) p d a b hX0 hp hd ha hb]
  dsimp [tupleMask,logMask,poolCuts,boxCuts]
  tauto

theorem coreBox_weight_eq_atoms (X s : ℝ) (p d a b i j : ℕ)
    (hX : 1<X) (hpP : p∈largePrimes X) (hp : 0<p)
    (hd : 0<d) (ha : 0<a) (hb : 0<b) :
    (if coreBoxSource X s d a b i j p then originalWeight X s true (p,d,[a,b]) else 0) =
      divisorAtom X s d p * (if tupleMask X s a b i j then (1:ℂ) else 0) *
        (if logMask X s d a b i j p then (1:ℂ) else 0) := by
  simp only [coreBoxSource_log_iff X s p d a b i j hX hp hd ha hb,hpP,true_and]
  by_cases hc : d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s <;>
    by_cases ht : tupleMask X s a b i j <;>
    by_cases hl : logMask X s d a b i j p <;>
    simp [divisorAtom,hc,ht,hl,originalWeight]

theorem completedBox_weight_eq_atoms (X s L R : ℝ) (p d a b i j k : ℕ)
    (hX : 1<X) (hpP : p∈largePrimes X) (hp : 0<p)
    (hd : 0<d) (ha : 0<a) (hb : 0<b) (hk : 0<k) (hL : 0<L) (hR : 0<R) :
    (if completedBoxSource X s d a b i j k L R p then
      originalWeight X s true (p,d,[a,b]) else 0) =
      divisorAtom X s d p * (if tupleMask X s a b i j then (1:ℂ) else 0) *
        (if logMask X s d a b i j p then (1:ℂ) else 0) *
        (if windowCuts L R (Real.log (p:ℝ)) (Real.log (d:ℝ))
          (Real.log (a:ℝ)) (Real.log (b:ℝ)) (Real.log (k:ℝ)) then (1:ℂ) else 0) := by
  have hw := completedWindow_log_iff p d a b k L R hp hd ha hb hk hL hR
  change completedWindow d a b k L R p ↔
    windowCuts L R (Real.log (p:ℝ)) (Real.log (d:ℝ))
      (Real.log (a:ℝ)) (Real.log (b:ℝ)) (Real.log (k:ℝ)) at hw
  rw [←coreBox_weight_eq_atoms X s p d a b i j hX hpP hp hd ha hb]
  simp only [completedBoxSource,←hw]
  by_cases hc : coreBoxSource X s d a b i j p <;>
    by_cases hw : completedWindow d a b k L R p <;> simp [hc,hw]

run_cmd do
  for decl in [``coreBoxSource_log_iff, ``coreBox_weight_eq_atoms,
      ``completedBox_weight_eq_atoms] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSeparatedLogMaskWork
