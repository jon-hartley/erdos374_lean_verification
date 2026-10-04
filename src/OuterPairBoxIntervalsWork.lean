import OuterPairFixedBoxesWork

/-! At a fixed grid index, the box membership of a fixed tuple prime is
order-convex in the outer prime. This is the interval structure needed to
separate the literal geometric box mask. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace OuterPairBoxIntervalsWork
open SieveGeometricGrid SieveWeightedCutoffs SieveBoxedFamily

private theorem level_antitone (X s : ℝ) (hX : 0<X) (p q : ℕ)
    (hp : 0<p) (hpq : p≤q) : level X s/q≤level X s/p := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hpqR : (p:ℝ)≤q := by exact_mod_cast hpq
  have hl : 0≤level X s := by unfold level; exact Real.rpow_nonneg hX.le _
  exact div_le_div_of_nonneg_left hl hpR hpqR

/-- As the outer prime grows, every fixed grid boundary moves downward. -/
theorem scale_antitone_outer (X s : ℝ) (hX : 0<X) (hs : 0<s)
    (p q i : ℕ) (hp : 0<p) (hpq : p≤q) :
    scale (level X s/q) s i≤scale (level X s/p) s i := by
  have hh := level_antitone X s hX p q hp hpq
  have he : 0≤exponent s i := by unfold exponent ratio; positivity
  unfold scale
  have hqR : (0:ℝ)≤q := by exact_mod_cast (show 0≤q by omega)
  have hbase : 0≤level X s/q := by
    unfold level
    exact div_nonneg (Real.rpow_nonneg hX.le _) hqR
  exact Real.rpow_le_rpow hbase hh he

/-- For a fixed grid index, membership holds at every intermediate outer
prime if it holds at both endpoints. -/
theorem inBox_convex_outer (X s : ℝ) (hX : 0<X) (hs : 0<s)
    (p q r i : ℕ) (hp : 0<p) (hpq : p≤q) (hqr : q≤r) (a : ℝ)
    (hpa : InBox (level X s/p) s a i)
    (hra : InBox (level X s/r) s a i) :
    InBox (level X s/q) s a i := by
  constructor
  · exact (scale_antitone_outer X s hX hs p q i hp hpq).trans hpa.1
  · exact hra.2.trans_le (scale_antitone_outer X s hX hs q r (i+1)
      (lt_of_lt_of_le hp hpq) hqr)

/-- Pool membership is also interval-shaped if its upper cutoff falls as
the outer prime increases. -/
theorem pool_convex_outer (X s : ℝ) (hX : 0<X) (hs : 0<s)
    (p q r a : ℕ) (hp : 0<p) (hpq : p≤q) (hqr : q≤r)
    (z : ℝ→ℝ) (hz : z r≤z q)
    (hpa : a∈pool (level X s/p) s (z p))
    (hra : a∈pool (level X s/r) s (z r)) :
    a∈pool (level X s/q) s (z q) := by
  obtain ⟨hprime,_,hlow⟩ := (mem_pool _ _ _ a).mp hpa
  obtain ⟨_,hupp,_⟩ := (mem_pool _ _ _ a).mp hra
  apply (mem_pool _ _ _ a).mpr
  refine ⟨hprime,hupp.trans_le hz,?_⟩
  have hlevel := level_antitone X s hX p q hp hpq
  have hqR : (0:ℝ)≤q := by exact_mod_cast (show 0≤q by omega)
  have hbase : 0≤level X s/q := by
    unfold level
    exact div_nonneg (Real.rpow_nonneg hX.le _) hqR
  exact (Real.rpow_le_rpow hbase hlevel (sq_nonneg s)).trans hlow

run_cmd do
  for decl in [``scale_antitone_outer, ``inBox_convex_outer, ``pool_convex_outer] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairBoxIntervalsWork
