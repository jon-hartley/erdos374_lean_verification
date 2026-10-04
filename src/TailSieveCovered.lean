import TailSieveProfiles
import PositiveSharpPowerWindow

/-! A complete signed sum over the covered arbitrary-length lower profiles.
All representation collisions survive collection. The enumeration bound
depends only on the already fixed s, not on X or the integration variable. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TailSieveCovered

abbrev Index := Bool × (List ℕ × ℕ)

def candidates (s:ℝ) : Finset Index :=
  Finset.univ ×ˢ ((SieveBoxedFamily.boundedTuples
    (Finset.range (SieveGeometricGrid.cutoff s+1)) (SieveBoxLength.cutoff s)) ×ˢ
      Finset.range (SieveGeometricGrid.cutoff s+1))

def family (X s:ℝ) : Finset Index := (candidates s).filter (fun a =>
  a.2.1≠[] ∧ a.2.1++[a.2.2]∈SieveBoxGrouping.profiles a.1 (SieveWeightedCutoffs.level X s) s ∧
  SieveGeometricGrid.scale (SieveWeightedCutoffs.level X s) s (a.2.2+1)≤X^(1/6:ℝ))

def componentSupport (X s z:ℝ) (a:Index) : Finset ℕ :=
  TailSieveProfileBasics.support (SieveWeightedCutoffs.level X s) s z a.2.1 a.2.2

def componentWeight (X s z:ℝ) (a:Index) (m:ℕ) : ℝ :=
  (if a.1 then -1 else 1) * TailSieveProfileBasics.coefficient
    (SieveWeightedCutoffs.level X s) s z (!a.1) a.2.1 a.2.2 m

def remainder (X s z L R:ℝ) : ℝ :=
  HarmanDivisorWindow.remainder
    (FiniteDivisorFamily.support (family X s) (componentSupport X s z))
    (FiniteDivisorFamily.coefficient (family X s) (componentSupport X s z) (componentWeight X s z)) L R

theorem snoc_injective : Function.Injective (fun a:List ℕ×ℕ => a.1++[a.2]) := by
  intro a b hab
  have hlen : a.1.length=b.1.length := by
    have hh := congrArg List.length hab
    simp only [List.length_append,List.length_singleton] at hh
    omega
  exact Prod.ext (List.append_inj_left hab hlen)
    (by simpa using List.append_inj_right hab hlen)

theorem component_remainder (X s z L R:ℝ) (a:Index) :
    HarmanDivisorWindow.remainder (componentSupport X s z a) (componentWeight X s z a) L R =
      (if a.1 then -1 else 1) * TailSieveProfileBasics.remainder
        (SieveWeightedCutoffs.level X s) s z (!a.1) a.2.1 a.2.2 L R :=
  FactoredDivisorScaling.remainder_scale _ _ _ _ _

theorem exact_profile_sum (X s z L R:ℝ) :
    remainder X s z L R = ∑a∈family X s,
      (if a.1 then -1 else 1) * MomentRemainderProfileSplit.profileRemainder
        (SieveWeightedCutoffs.level X s) s z (!a.1)
        (fun _ => a.2.1.length) (a.2.1++[a.2.2]) L R := by
  simp only [remainder,FiniteDivisorFamily.remainder_eq_sum,component_remainder,
    TailSieveProfileBasics.remainder_eq_profile]

theorem eventually_bound (s ε:ℝ) (hs:0<s) (hs1:s≤1/1000)
    (hε:0<ε) (hε1:ε<1/100) :
    ∃c:ℝ, 0<c ∧ ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀Y z:ℝ,
      X^FactoredDivisorHarmanRegion.windowExponent ε≤Y → Y≤X/2 →
      z≤SieveWeightedCutoffs.level X s →
      (1/X)*(∫x in Icc X (2*X),remainder X s z (x-x*(Y/X)) x ^2)≤Y^2*X^(-c) := by
  obtain ⟨c,hc,he⟩ := TailSieveProfiles.eventually_bound s ε hs hs1 hε hε1
  have hcard := (tendsto_rpow_atTop (show 0<c/4 by positivity)).eventually
    (eventually_ge_atTop ((candidates s).card:ℝ))
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [he,hcard] with X hb hcard
  refine ⟨hb.1,?_⟩
  intro Y z hY hYhalf hz
  have hX:0<X := by linarith [hb.1]
  have hY0:0≤Y := (Real.rpow_nonneg hX.le _).trans hY
  have hcard' : ((family X s).card:ℝ)≤X^(c/4) := by
    have hh : ((family X s).card:ℝ)≤((candidates s).card:ℝ) := by
      exact_mod_cast Finset.card_filter_le (candidates s) (fun a:Index =>
        a.2.1≠[] ∧ a.2.1++[a.2.2]∈SieveBoxGrouping.profiles a.1 (SieveWeightedCutoffs.level X s) s ∧
        SieveGeometricGrid.scale (SieveWeightedCutoffs.level X s) s (a.2.2+1)≤X^(1/6:ℝ))
    exact hh.trans hcard
  apply FiniteDivisorFamily.normalized_power_bound (family X s)
    (componentSupport X s z) (componentWeight X s z) X Y c hX hY0 (by linarith) hcard'
  intro a ha
  obtain ⟨hgnil,hg,hj⟩ := (Finset.mem_filter.mp ha).2
  have hh := hb.2 Y z a.1 a.2.1 a.2.2 hY hYhalf hz hgnil hg hj
  simp only [component_remainder]
  cases h : a.1 <;> simpa only [h,Bool.false_eq_true,ite_true,ite_false,one_mul,neg_one_mul,neg_sq] using hh

theorem eventually_half_width_bound (s:ℝ) (hs:0<s) (hs1:s≤1/1000) :
    ∃c:ℝ, 0<c ∧ ∀ᶠ X:ℝ in atTop, 1<X ∧ ∀z:ℝ,
      z≤SieveWeightedCutoffs.level X s →
      let Y:=PositiveSharpPowerWindow.halfWidth X (101/1000)
      (1/X)*(∫x in Icc X (2*X),remainder X s z (x-x*(Y/X)) x ^2)≤Y^2*X^(-c) := by
  obtain ⟨c,hc,he⟩ := eventually_bound s (1/2000) hs hs1 (by norm_num) (by norm_num)
  refine ⟨c,hc,?_⟩
  filter_upwards [he,PositiveSharpPowerWindow.halfWidth_eventually (101/1000) (by norm_num),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2000)).eventually (eventually_ge_atTop (2:ℝ))]
    with X hh hhalf hpow
  refine ⟨hh.1,?_⟩
  intro z hz
  apply hh.2 _ z _ (by linarith [hhalf.2]) hz
  have hX:0<X := by linarith [hh.1]
  have hm := mul_le_mul_of_nonneg_left hpow
    (Real.rpow_nonneg hX.le (FactoredDivisorHarmanRegion.windowExponent (1/2000)))
  rw [←Real.rpow_add hX] at hm
  have he : FactoredDivisorHarmanRegion.windowExponent (1/2000)+(1/2000)=(101/1000:ℝ) := by
    norm_num [FactoredDivisorHarmanRegion.windowExponent]
  rw [he] at hm
  dsimp [PositiveSharpPowerWindow.halfWidth]
  linarith

run_cmd do
  for decl in [``snoc_injective,``component_remainder,``exact_profile_sum,
      ``eventually_bound,``eventually_half_width_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SIGNED ALL-LENGTH COVERED LOWER-PROFILE COMPONENT POWER SAVING PASSED"

end TailSieveCovered
