import TailSieveProfileBasics
import CancellationSieveBlock
import FrontierGlobalData

/-! Mean-square saving for every actual lower-sieve profile of length at least
two whose final prime band has upper endpoint at most X^(8/35). Both signs
and their opposite small brackets are present. The length cap is fixed by s. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace FrontierSieveProfiles
open SieveBoxGrouping SieveGeometricGrid TailSieveProfileBasics
open FourPrimeScaleBudget

theorem eventually_bound (s ε : ℝ) (hs : 0<s) (hs1 : s≤1/1000)
    (hε : 0<ε) (hε1 : ε<1/100) :
    ∃c:ℝ, 0<c ∧ ∀ᶠ X:ℝ in atTop, 1<X ∧
      ∀(Y z:ℝ)(positive:Bool)(g:List ℕ)(j:ℕ),
        X^FactoredDivisorHarmanRegion.windowExponent ε≤Y → Y≤X/2 →
        z≤SieveWeightedCutoffs.level X s → g≠[] →
        g++[j]∈profiles positive (SieveWeightedCutoffs.level X s) s →
        scale (SieveWeightedCutoffs.level X s) s (j+1)≤X^(8/35:ℝ) →
        (1/X)*(∫x in Icc X (2*X),
          remainder (SieveWeightedCutoffs.level X s) s z (!positive) g j (x-x*(Y/X)) x ^2)
          ≤Y^2*X^(-c) := by
  have hs100 : s<1/100 := by linarith
  have hb := lowerExponent_pos s hs hs100
  obtain ⟨c,hc,hfamily⟩ := FactoredDivisorVariableWindow.eventually_bound
    (ι:=ℕ×ℕ) (lowerExponent s/2) (s/2) (s/2) (lowerExponent s/2) ε
    (by positivity) (by positivity) (by positivity) (by positivity) hε hε1
  refine ⟨c,hc,?_⟩
  filter_upwards [hfamily,eventually_divisor_fourth c hc,
    eventual_lower_bin_budget s hs hs100,
    FourPrimeGlobalPartition.eventually_family_cost c hc,
    eventually_left_coefficient_cap (SieveBoxLength.cutoff s) (c/2) (by positivity),
    eventually_gt_atTop (1:ℝ)] with X hf hdiv hbin hcost hcap hX
  refine ⟨hX,?_⟩
  intro Y z positive g j hY hYhalf hz hgnil hg hj
  let D := SieveWeightedCutoffs.level X s
  have hD : 1<D := Real.one_lt_rpow hX (by linarith)
  let S := leftSupport D s z g
  let T := primeBand D s z j
  let a := leftCoefficient D s z (!positive) g
  have hS : ∀m∈S,2≤m := left_positive D s z g hgnil
  have hT : ∀n∈T,2≤n := fun n hn => ((mem_primeBand D s z j n).mp hn).1.two_le
  have hlow : ∀n∈T,X^lowerExponent s≤(n:ℝ) := by
    intro n hn
    have hp := ((mem_primeBand_iff_index D s z hD hs hz j n).mp hn).1
    have hh := ((SieveBoxedFamily.mem_pool D s z n).mp hp).2.2
    simpa only [D,SieveWeightedCutoffs.level,
      ←Real.rpow_mul (show 0≤X by linarith),lowerExponent] using hh
  have hupp : ∀n∈T,(n:ℝ)≤X^(8/35:ℝ) :=
    fun n hn => ((mem_primeBand D s z j n).mp hn).2.2.2.le.trans hj
  have hprod : ∀m∈S,∀n∈T,(m:ℝ)*n≤X^(1-2*s) := by
    intro m hm n hn
    have hh := MomentRemainderSupport.lower_support_lt_power D s z hD hs
      (by linarith) hz (m*n) (product_mem_boxed positive D s z hD hs hz g j hg m hm n hn)
    have hh' : (m:ℝ)*n≤D^(MomentRemainderSupport.boxedExponent s) := by
      simpa only [Nat.cast_mul] using hh.le
    exact hh'.trans (MomentRemainderSupport.level_power_le X s hX.le hs.le (by linarith))
  by_cases hTempty : T=∅
  · have he : primeBand D s z j=∅ := hTempty
    have hzero (L R:ℝ) : remainder D s z (!positive) g j L R=0 := by
      simp only [remainder,support,FactoredDivisorWeights.support,
        HarmanDivisorWindow.productSupport,he,Finset.product_empty,Finset.image_empty,
        HarmanDivisorWindow.remainder_eq_sum,Finset.sum_empty]
    change (1/X)*(∫x in Icc X (2*X),remainder D s z (!positive) g j (x-x*(Y/X)) x ^2)≤_
    simp only [hzero,zero_pow (by decide : 2≠0),integral_zero,mul_zero]
    positivity
  have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTempty
  have hSup : ∀m∈S,(m:ℝ)≤X := by
    intro m hm
    obtain ⟨n,hn⟩ := hTne
    have hn1 : (1:ℝ)≤n := by exact_mod_cast (hT n hn).trans' (by norm_num : 1≤2)
    have hh := (hprod m hm n hn).trans (Real.rpow_le_self_of_one_le hX.le (by linarith))
    nlinarith [show (0:ℝ)≤m from Nat.cast_nonneg m]
  have hlen : g.length≤SieveBoxLength.cutoff s := by
    have hh := ((mem_profiles positive D s (g++[j])).mp hg).1
    simp only [List.length_append,List.length_singleton] at hh
    omega
  have ha : ∀m∈S,|a m|≤X^(c/2) := by
    intro m hm
    have hm0 : m≠0 := by have := hS m hm; omega
    exact hcap.2 D s z (!positive) g m hlen hm0
      ((hSup m hm).trans (by nlinarith [sq_nonneg (X-1)]))
  obtain ⟨hcoverS,hcoverT,hcard,hdata⟩ := FrontierGlobalData.global_data X s c hX.le hs hc
    hdiv.2 hbin.2 hcost.2 S T (fun _ => 0) (fun _ => 0) hTne hS hT hlow hupp hprod
    (by intro m _; simp only [abs_zero]; positivity) (by simp)
  let k := FourPrimeGlobalPartition.k X
  let F := FourPrimePartition.family S T 1 1 k k
  let M := fun ij:ℕ×ℕ => FourPrimePartition.scale 1 ij.1
  let N := fun ij:ℕ×ℕ => FourPrimePartition.scale 1 ij.2
  let sm := fun ij:ℕ×ℕ => FourPrimePartition.block S 1 ij.1
  let sn := fun ij:ℕ×ℕ => FourPrimePartition.block T 1 ij.2
  have hactual : ∀ij∈F,
      1≤M ij ∧ 1≤N ij ∧ X^(lowerExponent s/2)≤((M ij*N ij:ℕ):ℝ) ∧
      ((M ij*N ij:ℕ):ℝ)≤X^(1-s/2-s/2) ∧ X^(lowerExponent s/2)≤(N ij:ℝ) ∧
      ((N ij:ℝ)≤X^(8/35:ℝ) ∨ X^(27/35:ℝ)≤((M ij*N ij:ℕ):ℝ)) ∧
      (∀m∈sm ij,M ij<m ∧ m≤2*M ij) ∧ (∀n∈sn ij,N ij<n ∧ n≤2*N ij) ∧
      (∀m∈sm ij,|a m|≤X^(c/2)) ∧ (∀n∈sn ij,|(1:ℝ)|≤X^(c/2)) := by
    intro ij hij
    obtain ⟨hM,hN,hAl,hAu,hNl,hbranch,hsm,hsn,_,_⟩ := hdata ij hij
    refine ⟨hM,hN,hAl,hAu,hNl,hbranch,hsm,hsn,?_,?_⟩
    · intro m hm
      exact ha m ((FourPrimePartition.mem_block S 1 ij.1 m).mp hm).1
    · intro n _
      simpa only [abs_one] using Real.one_le_rpow hX.le (show 0≤c/2 by positivity)
  have hh := hf.2 Y F M N sm sn (fun _ => a) (fun _ _ => 1) hY hYhalf hcard hactual
  simpa only [F,M,N,sm,sn,
    FourPrimePartition.remainder_family_eq S T 1 1 k k a (fun _ => 1) hcoverS hcoverT,
    remainder,support,coefficient,S,T,a,D] using hh

run_cmd do
  for ax in (←Lean.collectAxioms ``eventually_bound) do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo "FRONTIER ACTUAL ARBITRARY-LENGTH PROFILE SAVING THROUGH EIGHT THIRTY-FIFTHS PASSED"

end FrontierSieveProfiles
