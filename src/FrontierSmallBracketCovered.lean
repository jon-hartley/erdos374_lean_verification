import FrontierSmallBracket
import PositiveSharpPowerWindow

/-! Uniform finite-subfamily aggregation of the truncated small-bracket
profile estimate. The source signs and every collected representation remain.
The subfamily is chosen after X; its count is bounded by the fixed-s inventory.
No estimate is asserted for the omitted small-divisor range. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FrontierSmallBracketCovered

abbrev Index := Bool × List ℕ

def candidates (s : ℝ) : Finset Index :=
  Finset.univ ×ˢ SieveBoxedFamily.boundedTuples
    (Finset.range (SieveGeometricGrid.cutoff s+1)) (SieveBoxLength.cutoff s)

def family (X s : ℝ) : Finset Index := (candidates s).filter (fun a =>
  a.2≠[] ∧ a.2∈SieveBoxGrouping.profiles a.1 (SieveWeightedCutoffs.level X s) s)

theorem mem_family_iff (X s : ℝ) (a : Index) : a∈family X s ↔
    a.2≠[] ∧ a.2∈SieveBoxGrouping.profiles a.1 (SieveWeightedCutoffs.level X s) s := by
  constructor
  · exact fun ha => (Finset.mem_filter.mp ha).2
  · intro ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,?_⟩,ha⟩
    obtain ⟨hlen,hindices,_⟩ := (SieveBoxGrouping.mem_profiles _ _ _ _).mp ha.2
    apply (SieveBoxedFamily.mem_boundedTuples _ _ _).mpr
    exact ⟨hlen,fun i hi => Finset.mem_range.mpr (Nat.lt_succ_of_le (hindices i hi))⟩

def componentSupport (X s z : ℝ) (a : Index) : Finset ℕ :=
  FrontierSmallBracket.support X s z a.2

def componentWeight (X s z : ℝ) (a : Index) (m : ℕ) : ℝ :=
  (if a.1 then -1 else 1)*FrontierSmallBracket.coefficient X s z (!a.1) a.2 m

def remainder (X s z : ℝ) (F : Finset Index) (L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder
    (FiniteDivisorFamily.support F (componentSupport X s z))
    (FiniteDivisorFamily.coefficient F (componentSupport X s z) (componentWeight X s z)) L R

theorem component_remainder (X s z L R : ℝ) (a : Index) :
    HarmanDivisorWindow.remainder (componentSupport X s z a) (componentWeight X s z a) L R=
      (if a.1 then -1 else 1)*FrontierSmallBracket.remainder X s z (!a.1) a.2 L R :=
  FactoredDivisorScaling.remainder_scale _ _ _ _ _

theorem remainder_eq_sum (X s z L R : ℝ) (F : Finset Index) :
    remainder X s z F L R=∑a∈F,
      (if a.1 then -1 else 1)*FrontierSmallBracket.remainder X s z (!a.1) a.2 L R := by
  simp only [remainder,FiniteDivisorFamily.remainder_eq_sum,component_remainder]

theorem eventually_bound (s ε : ℝ) (hs : 0<s) (hs1 : s≤1/1000)
    (hε : 0<ε) (hε1 : ε<1/100) :
    ∃c:ℝ, 0<c ∧ ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀(Y z:ℝ)(F:Finset Index),
      X^FactoredDivisorHarmanRegion.windowExponent ε≤Y → Y≤X/2 →
      z≤SieveWeightedCutoffs.level X s → F⊆family X s →
      (1/X)*(∫x in Icc X (2*X),remainder X s z F (x-x*(Y/X)) x ^2)≤Y^2*X^(-c) := by
  obtain ⟨c,hc,he⟩ := FrontierSmallBracket.eventually_bound s ε hs hs1 hε hε1
  have hcard := (tendsto_rpow_atTop (show 0<c/4 by positivity)).eventually
    (eventually_ge_atTop ((candidates s).card:ℝ))
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [he,hcard] with X hb hcard
  refine ⟨hb.1,?_⟩
  intro Y z F hY hYhalf hz hF
  have hX : 0<X := by linarith [hb.1]
  have hY0 : 0≤Y := (Real.rpow_nonneg hX.le _).trans hY
  have hcard' : (F.card:ℝ)≤X^(c/4) := by
    have hh : (F.card:ℝ)≤((candidates s).card:ℝ) := by
      exact_mod_cast Finset.card_le_card (hF.trans (Finset.filter_subset _ _))
    exact hh.trans hcard
  apply FiniteDivisorFamily.normalized_power_bound F
    (componentSupport X s z) (componentWeight X s z) X Y c hX hY0 (by linarith) hcard'
  intro a ha
  obtain ⟨hne,hg⟩ := (mem_family_iff X s a).mp (hF ha)
  have hh := hb.2 Y z a.1 a.2 hY hYhalf hz hne hg
  simp only [component_remainder]
  cases h : a.1 <;> simpa [h] using hh

theorem eventually_half_width_bound (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∃c:ℝ, 0<c ∧ ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀(z:ℝ)(F:Finset Index),
      z≤SieveWeightedCutoffs.level X s → F⊆family X s →
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),remainder X s z F (x-x*(Y/X)) x ^2)≤Y^2*X^(-c) := by
  obtain ⟨c,hc,he⟩ := eventually_bound s (1/2000) hs hs1 (by norm_num) (by norm_num)
  refine ⟨c,hc,?_⟩
  filter_upwards [he,PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2000)).eventually (eventually_ge_atTop (2:ℝ))]
    with X hh hhalf hpow
  refine ⟨hh.1,?_⟩
  intro z F hz hF
  apply hh.2 _ z F _ (by linarith [hhalf.2]) hz hF
  have hX : 0<X := by linarith [hh.1]
  have hm := mul_le_mul_of_nonneg_left hpow
    (Real.rpow_nonneg hX.le (FactoredDivisorHarmanRegion.windowExponent (1/2000)))
  rw [←Real.rpow_add hX] at hm
  have he : FactoredDivisorHarmanRegion.windowExponent (1/2000)+(1/2000)=(101/1000:ℝ) := by
    norm_num [FactoredDivisorHarmanRegion.windowExponent]
  rw [he] at hm
  dsimp [PositiveSharpPowerWindow.halfWidth]
  linarith

run_cmd do
  for decl in [``mem_family_iff,``component_remainder,``remainder_eq_sum,
      ``eventually_bound,``eventually_half_width_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL TRUNCATED SMALL-BRACKET ARBITRARY-SUBFAMILY SAVING PASSED"

end FrontierSmallBracketCovered
