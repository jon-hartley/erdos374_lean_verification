import OuterPairBoxGateWork

/-! The first-coordinate outer pair gate is downward stable as the
outer-prime-dependent sieve level decreases. The pair-order condition is
not covered by this statement. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace OuterPairBoxMonotoneWork
open SieveGeometricGrid SieveBoxTuples SieveBoxedFamily SieveWeightedCutoffs

/-- Decreasing the level can only increase the box index of a fixed entry
while that entry remains in both admissible ranges. -/
theorem boxIndex_anti_level (Dlo Dhi s q : ℝ) (hlo : 1<Dlo)
    (hhi : 1<Dhi) (hlevels : Dlo≤Dhi) (hs : 0<s)
    (hqlow : Dlo^(s^2)≤q) (hqupLow : q<Dlo)
    (hqhigh : Dhi^(s^2)≤q) (hqupHigh : q<Dhi) :
    boxIndex Dhi s q≤boxIndex Dlo s q := by
  let i := boxIndex Dhi s q
  let j := boxIndex Dlo s q
  have hi := boxIndex_spec Dhi s q hhi hs hqhigh hqupHigh
  have hj := boxIndex_spec Dlo s q hlo hs hqlow hqupLow
  have he : 0≤exponent s i := by
    unfold exponent ratio
    positivity
  have hscale : scale Dlo s i≤scale Dhi s i := by
    unfold scale
    exact Real.rpow_le_rpow (by linarith) hlevels he
  by_contra h
  have hji : j < i := by omega
  have hmono : scale Dlo s (j+1)≤scale Dlo s i :=
    (scale_strictMono Dlo s hlo hs).monotone (by omega)
  exact (not_lt_of_ge (hscale.trans hi.1)) (hj.2.trans_le hmono)

/-- The numerical outer pair gate is downward stable in the level. -/
theorem gate_anti_level (Dlo Dhi s q : ℝ) (hlo : 1<Dlo)
    (hhi : 1<Dhi) (hlevels : Dlo≤Dhi) (hs : 0<s)
    (hqlow : Dlo^(s^2)≤q) (hqupLow : q<Dlo)
    (hqhigh : Dhi^(s^2)≤q) (hqupHigh : q<Dhi)
    (hgate : 3*exponent s (boxIndex Dlo s q)<1) :
    3*exponent s (boxIndex Dhi s q)<1 := by
  have hind := boxIndex_anti_level Dlo Dhi s q hlo hhi hlevels hs
    hqlow hqupLow hqhigh hqupHigh
  have hr : 1≤ratio s := (one_lt_ratio s hs).le
  have he : exponent s (boxIndex Dhi s q)≤exponent s (boxIndex Dlo s q) := by
    unfold exponent
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hind) (sq_nonneg s)
  linarith


/-- On the actual outer-prime scale, the first-coordinate box gate remains
true when the outer prime is decreased, provided the tuple entry remains
in both literal prime pools. -/
theorem original_gate_stable_downward (X s : ℝ) (hX : 0<X) (hs : 0<s)
    (p q a : ℕ) (hp : 0<p) (hpq : p≤q) (z : ℝ→ℝ)
    (hDp : 1<level X s/p) (hDq : 1<level X s/q)
    (hzp : z p≤level X s/p) (hzq : z q≤level X s/q)
    (hap : a∈pool (level X s/p) s (z p))
    (haq : a∈pool (level X s/q) s (z q))
    (hg : 3*exponent s (boxIndex (level X s/q) s (a:ℝ))<1) :
    3*exponent s (boxIndex (level X s/p) s (a:ℝ))<1 := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hqR : (0:ℝ)<q := by exact_mod_cast (lt_of_lt_of_le hp hpq)
  have hpqR : (p:ℝ)≤q := by exact_mod_cast hpq
  have hlevel : 0≤level X s := by unfold level; exact Real.rpow_nonneg hX.le _
  have hD : level X s/q≤level X s/p :=
    div_le_div_of_nonneg_left hlevel hpR hpqR
  obtain ⟨_,haqz,haql⟩ := (mem_pool _ _ _ a).mp haq
  obtain ⟨_,hapz,hapl⟩ := (mem_pool _ _ _ a).mp hap
  exact gate_anti_level (level X s/q) (level X s/p) s (a:ℝ)
    hDq hDp hD hs haql (haqz.trans_le hzq) hapl (hapz.trans_le hzp) hg

run_cmd do
  for decl in [``boxIndex_anti_level, ``gate_anti_level, ``original_gate_stable_downward] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairBoxMonotoneWork
