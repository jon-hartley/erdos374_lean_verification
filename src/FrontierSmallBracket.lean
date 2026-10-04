import FrontierGlobalData
import TailSieveProfileBasics
import CancellationSieveBlock

/-! A literal truncated small-bracket contribution of every nonempty actual
lower-sieve profile. The complete tuple multiplicity is on the left; the
actual small weight is on the right. Small divisors below the stated threshold,
including 1, are not estimated here. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FrontierSmallBracket
open SieveBoxGrouping SieveTupleConvolution FourPrimeScaleBudget

def leftSupport (X s z : ℝ) (h : List ℕ) : Finset ℕ :=
  tupleSupport (fibre (SieveWeightedCutoffs.level X s) s z h)

def rightSupport (X s : ℝ) : Finset ℕ :=
  (SieveUpperBoxWindow.smallCarrier (SieveWeightedCutoffs.level X s) s).filter
    (fun d => X^lowerExponent s≤(d:ℝ))

def leftCoefficient (X s z : ℝ) (h : List ℕ) : ℕ→ℝ :=
  tupleCoefficient (fibre (SieveWeightedCutoffs.level X s) s z h)

def smallWeight (X s : ℝ) (upper : Bool) : ℕ→ℝ :=
  SieveSmallWeights.weight ((SieveWeightedCutoffs.level X s)^s)
    ((SieveWeightedCutoffs.level X s)^(s^2)) upper

def support (X s z : ℝ) (h : List ℕ) : Finset ℕ :=
  FactoredDivisorWeights.support (leftSupport X s z h) (rightSupport X s)

def coefficient (X s z : ℝ) (upper : Bool) (h : List ℕ) : ℕ→ℝ :=
  FactoredDivisorWeights.coefficient (leftSupport X s z h) (rightSupport X s)
    (leftCoefficient X s z h) (smallWeight X s upper)

def remainder (X s z : ℝ) (upper : Bool) (h : List ℕ) (L R : ℝ) : ℝ :=
  HarmanDivisorWindow.remainder (support X s z h) (coefficient X s z upper h) L R

theorem kernel (X s z : ℝ) (upper : Bool) (h : List ℕ) (f : ℕ→ℝ) :
    (∑m∈support X s z h,coefficient X s z upper h m*f m)=
      ∑d∈rightSupport X s,∑t∈fibre (SieveWeightedCutoffs.level X s) s z h,
        smallWeight X s upper d*f (d*t.prod) := by
  rw [support,coefficient,FactoredDivisorWeights.support,
    FactoredDivisorWeights.grouped_sum _ _ _ _ _ _
      (HarmanDivisorWindow.productSupport_contains _ _),Finset.sum_product]
  simp only [DirichletProductCoefficients.productIndex]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  calc
    _ = ∑m∈leftSupport X s z h,leftCoefficient X s z h m*
        (smallWeight X s upper d*f (d*m)) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Nat.mul_comm m d]
      ring
    _ = _ := tuple_kernel _ _

theorem tuple_coefficient_as_signed (T : Finset (List ℕ)) (m : ℕ) :
    signedCoefficient {1} (fun _ => 1) (fun _ => 0) T ∅ m=tupleCoefficient T m := by
  rw [signedCoefficient,
    ←PositiveSharpRemainderAnalysis.collected_eq_convolution {1} _ (fun _ => 1) T
      (support_subset_tupleCarrier_left T ∅),
    ←PositiveSharpRemainderAnalysis.collected_eq_convolution {1} _ (fun _ => 0) ∅
      (support_subset_tupleCarrier_right T ∅)]
  simp only [PositiveSharpRemainderAnalysis.collected,PositiveSharpRemainderAnalysis.representations,
    tupleCoefficient,Finset.sum_filter,Finset.sum_product]
  simp

theorem eventually_tuple_coefficient_cap (K : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ X:ℝ in atTop, 1≤X ∧ ∀(T:Finset (List ℕ))(m:ℕ),
      m≠0 → (m:ℝ)≤X^2 → (∀t∈T,t.length≤K) → |tupleCoefficient T m|≤X^δ := by
  filter_upwards [PositiveSharpRemainderAnalysis.eventually_signedCoefficient_cap K δ hδ]
    with X hh
  refine ⟨hh.1,?_⟩
  intro T m hm hmX hlen
  have hc := hh.2 {1} (fun _ => 1) (fun _ => 0) T ∅ m hm hmX hlen
    (by simp) (by simp) (by simp)
  simpa only [tuple_coefficient_as_signed] using hc

theorem left_positive (X s z : ℝ) (h : List ℕ) (hne : h≠[]) (m : ℕ)
    (hm : m∈leftSupport X s z h) : 2≤m := by
  obtain ⟨t,ht,rfl⟩ := (mem_tupleSupport _ _).mp hm
  have hlen := ((mem_fibre _ _ _ _ _).mp ht).length_eq
  have htnil : t≠[] := by
    intro he
    simp only [he,List.length_nil] at hlen
    exact hne (List.length_eq_zero_iff.mp hlen.symm)
  have hp : ∀p∈t,2≤p := by
    have hrel : List.Forall₂ (fun (p i:ℕ) => 2≤p ∧ True) t h :=
      List.Forall₂.imp (fun p i h => ⟨((mem_primeBand _ _ _ i p).mp h).1.two_le,trivial⟩)
        ((mem_fibre _ _ _ _ _).mp ht)
    exact ((List.forall₂_and_left t h).mp hrel).1
  obtain ⟨p,ps,rfl⟩ := List.exists_cons_of_ne_nil htnil
  have hp2 := hp p (by simp)
  have hps : 0<ps.prod := List.prod_pos (fun q hq => by have := hp q (by simp [hq]); omega)
  simp only [List.prod_cons]
  nlinarith

theorem product_mem_boxed (positive : Bool) (X s z : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hz : z≤SieveWeightedCutoffs.level X s) (h : List ℕ)
    (hg : h∈profiles positive (SieveWeightedCutoffs.level X s) s)
    (m : ℕ) (hm : m∈leftSupport X s z h) (d : ℕ) (hd : d∈rightSupport X s) :
    m*d∈SieveBoxedWindow.support (SieveWeightedCutoffs.level X s) s z := by
  have hD : 1<SieveWeightedCutoffs.level X s := Real.one_lt_rpow hX (by linarith)
  obtain ⟨t,ht,he⟩ := (mem_tupleSupport _ _).mp hm
  rw [fibre_eq_filter positive _ s z hD hs hz h hg] at ht
  have hfamily := (Finset.mem_filter.mp ht).1
  have hunion : t∈SieveCompleteBoxing.innerFamily (SieveWeightedCutoffs.level X s) s z ∪
      SieveCompleteBoxing.outerFamily (SieveWeightedCutoffs.level X s) s z := by
    cases positive
    · exact Finset.mem_union_right _ hfamily
    · exact Finset.mem_union_left _ hfamily
  refine Finset.mem_image.mpr ⟨(d,m),Finset.mem_product.mpr
    ⟨(Finset.mem_filter.mp hd).1,(mem_tupleSupport _ _).mpr ⟨t,hunion,he⟩⟩,?_⟩
  exact Nat.mul_comm d m

theorem eventually_bound (s ε : ℝ) (hs : 0<s) (hs1 : s≤1/1000)
    (hε : 0<ε) (hε1 : ε<1/100) :
    ∃c:ℝ, 0<c ∧ ∀ᶠ X:ℝ in atTop, 1<X ∧
      ∀(Y z:ℝ)(positive:Bool)(h:List ℕ),
        X^FactoredDivisorHarmanRegion.windowExponent ε≤Y → Y≤X/2 →
        z≤SieveWeightedCutoffs.level X s → h≠[] →
        h∈profiles positive (SieveWeightedCutoffs.level X s) s →
        (1/X)*(∫x in Icc X (2*X),
          remainder X s z (!positive) h (x-x*(Y/X)) x ^2)≤Y^2*X^(-c) := by
  have hs100 : s<1/100 := by linarith
  have hb := lowerExponent_pos s hs hs100
  obtain ⟨c,hc,hfamily⟩ := FactoredDivisorVariableWindow.eventually_bound
    (ι:=ℕ×ℕ) (lowerExponent s/2) (s/2) (s/2) (lowerExponent s/2) ε
    (by positivity) (by positivity) (by positivity) (by positivity) hε hε1
  refine ⟨c,hc,?_⟩
  filter_upwards [hfamily,eventually_divisor_fourth c hc,
    eventual_lower_bin_budget s hs hs100,
    FourPrimeGlobalPartition.eventually_family_cost c hc,
    eventually_tuple_coefficient_cap (SieveBoxLength.cutoff s) (c/2) (by positivity),
    eventually_gt_atTop (1:ℝ)] with X hf hdiv hbin hcost hcap hX
  refine ⟨hX,?_⟩
  intro Y z positive h hY hYhalf hz hne hg
  let D := SieveWeightedCutoffs.level X s
  have hD : 1<D := Real.one_lt_rpow hX (by linarith)
  let S := leftSupport X s z h
  let T := rightSupport X s
  let a := leftCoefficient X s z h
  let b := smallWeight X s (!positive)
  have hS : ∀m∈S,2≤m := left_positive X s z h hne
  have hlow : ∀d∈T,X^lowerExponent s≤(d:ℝ) := fun d hd => (Finset.mem_filter.mp hd).2
  have hT : ∀d∈T,2≤d := by
    intro d hd
    have hh : (1:ℝ)<d := (Real.one_lt_rpow hX hb).trans_le (hlow d hd)
    have hh' : 1<d := by exact_mod_cast hh
    omega
  have hupp : ∀d∈T,(d:ℝ)≤X^(8/35:ℝ) := by
    intro d hd
    have hdD := PositiveSharpRemainderSupportGeometry.smallCarrier_lt D s hD hs
      (by linarith) d (Finset.mem_filter.mp hd).1
    apply hdD.le.trans
    dsimp [D,SieveWeightedCutoffs.level]
    rw [←Real.rpow_mul (show 0≤X by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by nlinarith [sq_nonneg s])
  have hprod : ∀m∈S,∀d∈T,(m:ℝ)*d≤X^(1-2*s) := by
    intro m hm d hd
    have hh := MomentRemainderSupport.lower_support_lt_power D s z hD hs
      (by linarith) hz (m*d) (product_mem_boxed positive X s z hX hs hs1 hz h hg m hm d hd)
    have hh' : (m:ℝ)*d≤D^(MomentRemainderSupport.boxedExponent s) := by
      simpa only [Nat.cast_mul] using hh.le
    exact hh'.trans (MomentRemainderSupport.level_power_le X s hX.le hs.le (by linarith))
  by_cases hTempty : T=∅
  · have he : rightSupport X s=∅ := hTempty
    have hzero (L R:ℝ) : remainder X s z (!positive) h L R=0 := by
      simp only [remainder,support,FactoredDivisorWeights.support,
        HarmanDivisorWindow.productSupport,he,Finset.product_empty,Finset.image_empty,
        HarmanDivisorWindow.remainder_eq_sum,Finset.sum_empty]
    simp only [hzero,zero_pow (by decide : 2≠0),integral_zero,mul_zero]
    positivity
  have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTempty
  have hSup : ∀m∈S,(m:ℝ)≤X := by
    intro m hm
    obtain ⟨d,hd⟩ := hTne
    have hd1 : (1:ℝ)≤d := by exact_mod_cast (hT d hd).trans' (by norm_num : 1≤2)
    have hh := (hprod m hm d hd).trans (Real.rpow_le_self_of_one_le hX.le (by linarith))
    nlinarith [show (0:ℝ)≤m from Nat.cast_nonneg m]
  have hlen : ∀t∈fibre D s z h,t.length≤SieveBoxLength.cutoff s := by
    intro t ht
    exact (((mem_fibre D s z h t).mp ht).length_eq).le.trans
      ((mem_profiles positive D s h).mp hg).1
  have ha : ∀m∈S,|a m|≤X^(c/2) := by
    intro m hm
    have hm0 : m≠0 := by have := hS m hm; omega
    exact hcap.2 _ m hm0 ((hSup m hm).trans (by nlinarith [sq_nonneg (X-1)])) hlen
  have hbweight : ∀d∈T,|b d|≤X^(c/2) := by
    intro d _
    exact (SieveSmallWeights.weight_abs_le_one _ _ _ d).trans
      (Real.one_le_rpow hX.le (by positivity))
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
      (∀m∈sm ij,M ij<m ∧ m≤2*M ij) ∧ (∀d∈sn ij,N ij<d ∧ d≤2*N ij) ∧
      (∀m∈sm ij,|a m|≤X^(c/2)) ∧ (∀d∈sn ij,|b d|≤X^(c/2)) := by
    intro ij hij
    obtain ⟨hM,hN,hAl,hAu,hNl,hbranch,hsm,hsn,_,_⟩ := hdata ij hij
    exact ⟨hM,hN,hAl,hAu,hNl,hbranch,hsm,hsn,
      fun m hm => ha m ((FourPrimePartition.mem_block S 1 ij.1 m).mp hm).1,
      fun d hd => hbweight d ((FourPrimePartition.mem_block T 1 ij.2 d).mp hd).1⟩
  have hh := hf.2 Y F M N sm sn (fun _ => a) (fun _ => b) hY hYhalf hcard hactual
  simpa only [F,M,N,sm,sn,
    FourPrimePartition.remainder_family_eq S T 1 1 k k a b hcoverS hcoverT,
    remainder,support,coefficient,S,T,a,b] using hh

run_cmd do
  for decl in [``kernel,``tuple_coefficient_as_signed,``eventually_tuple_coefficient_cap,
      ``left_positive,``product_mem_boxed,``eventually_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL TRUNCATED SMALL-BRACKET PROFILE SAVING PASSED"

end FrontierSmallBracket
