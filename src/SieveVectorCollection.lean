import SieveVectorDivisor
import FactoredDivisorWeights
import Mathlib.Data.Nat.GCD.BigOperators

/-! Exact two-coordinate coefficient collection. Coprime carriers give unique
factor splits and hence a unit bound; all finite convolution representations
are retained. No selector, support level, or sieve main term is assumed here. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators

namespace SieveVectorCollection

def lowerCoefficient (S T : Finset ℕ) (l0 u0 l1 u1 : ℕ → ℝ) (m : ℕ) : ℝ :=
  FactoredDivisorWeights.coefficient S T l0 u1 m +
    FactoredDivisorWeights.coefficient S T u0 l1 m -
      FactoredDivisorWeights.coefficient S T u0 u1 m

def collect {α : Type*} (S : Finset α) (key : α → ℕ) (w : α → ℝ) (m : ℕ) : ℝ :=
  ∑ x ∈ S.filter (fun x => key x = m), w x

theorem collect_abs_le_one {α : Type*} [DecidableEq α] (S : Finset α)
    (key : α → ℕ) (w : α → ℝ) (m : ℕ) (hi : Set.InjOn key (↑S))
    (hw : ∀ x ∈ S, |w x| ≤ 1) : |collect S key w m| ≤ 1 := by
  by_cases he : ∃ x ∈ S, key x = m
  · obtain ⟨x, hx, hxm⟩ := he
    have hxF : x ∈ S.filter (fun y => key y = m) := Finset.mem_filter.mpr ⟨hx, hxm⟩
    have hv : collect S key w m = w x := by
      unfold collect
      apply Finset.sum_eq_single_of_mem x hxF
      intro y hy hne
      obtain ⟨hyS, hym⟩ := Finset.mem_filter.mp hy
      exact (hne (hi hyS hx (hym.trans hxm.symm))).elim
    rw [hv]
    exact hw x hx
  · have hf : S.filter (fun x => key x = m) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (by simpa using he)
    simp [collect, hf]

theorem coprime_product_injective (S T : Finset ℕ)
    (hS : ∀ v ∈ S, 0 < v) (hc : ∀ v ∈ S, ∀ w ∈ T, v.Coprime w) :
    Set.InjOn (fun p : ℕ×ℕ => p.1*p.2) (↑(S.product T)) := by
  intro p hp q hq he
  change p.1*p.2 = q.1*q.2 at he
  obtain ⟨hpS, hpT⟩ := Finset.mem_product.mp hp
  obtain ⟨hqS, hqT⟩ := Finset.mem_product.mp hq
  have h1 : p.1 ∣ q.1 := (hc p.1 hpS q.2 hqT).dvd_of_dvd_mul_right
    (by rw [← he]; exact Nat.dvd_mul_right p.1 p.2)
  have h2 : q.1 ∣ p.1 := (hc q.1 hqS p.2 hpT).dvd_of_dvd_mul_right
    (by rw [he]; exact Nat.dvd_mul_right q.1 q.2)
  have hfirst : p.1 = q.1 := Nat.dvd_antisymm h1 h2
  have hsecond : p.2 = q.2 := by
    apply Nat.eq_of_mul_eq_mul_left (hS p.1 hpS)
    simpa only [← hfirst] using he
  exact Prod.ext hfirst hsecond

theorem lowerCoefficient_eq_collect (S T : Finset ℕ) (l0 u0 l1 u1 : ℕ → ℝ) (m : ℕ) :
    lowerCoefficient S T l0 u0 l1 u1 m =
      collect (S.product T) (fun p => p.1*p.2)
        (fun p => SieveVector.lowerKernel (l0 p.1) (u0 p.1) (l1 p.2) (u1 p.2)) m := by
  simp only [lowerCoefficient, FactoredDivisorWeights.coefficient,
    DirichletProductCoefficients.productIndex, collect, SieveVector.lowerKernel,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rfl

theorem lowerCoefficient_abs_le_one (S T : Finset ℕ) (l0 u0 l1 u1 : ℕ → ℝ)
    (hS : ∀ v ∈ S, 0 < v) (hc : ∀ v ∈ S, ∀ w ∈ T, v.Coprime w)
    (h0 : ∀ v ∈ S, |l0 v| ≤ 1 ∧ |u0 v| ≤ 1 ∧ (l0 v = 0 ∨ u0 v = 0 ∨ l0 v = u0 v))
    (h1 : ∀ w ∈ T, |l1 w| ≤ 1 ∧ |u1 w| ≤ 1 ∧ (l1 w = 0 ∨ u1 w = 0 ∨ l1 w = u1 w))
    (m : ℕ) : |lowerCoefficient S T l0 u0 l1 u1 m| ≤ 1 := by
  rw [lowerCoefficient_eq_collect]
  apply collect_abs_le_one _ _ _ _ (coprime_product_injective S T hS hc)
  intro p hp
  obtain ⟨hpS, hpT⟩ := Finset.mem_product.mp hp
  exact SieveVector.lowerKernel_abs_le_one _ _ _ _ (h0 _ hpS).1 (h0 _ hpS).2.1
    (h1 _ hpT).1 (h1 _ hpT).2.1 (h0 _ hpS).2.2 (h1 _ hpT).2.2

theorem upperCoefficient_abs_le_one (S T : Finset ℕ) (f g : ℕ → ℝ)
    (hS : ∀ v ∈ S, 0 < v) (hc : ∀ v ∈ S, ∀ w ∈ T, v.Coprime w)
    (hf : ∀ v ∈ S, |f v| ≤ 1) (hg : ∀ w ∈ T, |g w| ≤ 1) (m : ℕ) :
    |FactoredDivisorWeights.coefficient S T f g m| ≤ 1 := by
  change |collect (S.product T) (fun p => p.1*p.2) (fun p => f p.1*g p.2) m| ≤ 1
  apply collect_abs_le_one _ _ _ _ (coprime_product_injective S T hS hc)
  intro p hp
  obtain ⟨hpS, hpT⟩ := Finset.mem_product.mp hp
  rw [abs_mul]
  simpa using mul_le_mul (hf _ hpS) (hg _ hpT) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)

theorem coprime_mul_dvd_iff (m k n : ℕ) (hc : m.Coprime k) :
    m*k ∣ n ↔ m ∣ n ∧ k ∣ n := by
  constructor
  · intro h
    exact ⟨(Nat.dvd_mul_right m k).trans h, (Nat.dvd_mul_left k m).trans h⟩
  · rintro ⟨hm, hk⟩
    exact hc.mul_dvd_of_dvd_of_dvd hm hk

theorem convolution_evaluation (S T : Finset ℕ) (f g : ℕ → ℝ)
    (hc : ∀ m ∈ S, ∀ k ∈ T, m.Coprime k) (n : ℕ) :
    SieveDivisorWindow.evaluation (FactoredDivisorWeights.support S T)
      (FactoredDivisorWeights.coefficient S T f g) n =
        SieveDivisorWindow.evaluation S f n * SieveDivisorWindow.evaluation T g n := by
  have hh := FactoredDivisorWeights.grouped_sum S T (FactoredDivisorWeights.support S T)
    f g (fun d => if d ∣ n then (1 : ℝ) else 0)
    (HarmanDivisorWindow.productSupport_contains S T)
  simp only [mul_ite, mul_one, mul_zero] at hh
  unfold SieveDivisorWindow.evaluation
  rw [hh, Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  change (if m*k ∣ n then f m*g k else 0) = (if m ∣ n then f m else 0) *
    (if k ∣ n then g k else 0)
  have hd := coprime_mul_dvd_iff m k n (hc m hm k hk)
  by_cases hmD : m ∣ n <;> by_cases hkD : k ∣ n <;> simp [hd, hmD, hkD]

theorem evaluation_add (S : Finset ℕ) (f g : ℕ → ℝ) (n : ℕ) :
    SieveDivisorWindow.evaluation S (fun d => f d + g d) n =
      SieveDivisorWindow.evaluation S f n + SieveDivisorWindow.evaluation S g n := by
  simp only [SieveDivisorWindow.evaluation, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> ring

theorem evaluation_sub (S : Finset ℕ) (f g : ℕ → ℝ) (n : ℕ) :
    SieveDivisorWindow.evaluation S (fun d => f d - g d) n =
      SieveDivisorWindow.evaluation S f n - SieveDivisorWindow.evaluation S g n := by
  simp only [SieveDivisorWindow.evaluation, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> ring

theorem lowerCoefficient_evaluation (S T : Finset ℕ) (l0 u0 l1 u1 : ℕ → ℝ)
    (hc : ∀ m ∈ S, ∀ k ∈ T, m.Coprime k) (n : ℕ) :
    SieveDivisorWindow.evaluation (FactoredDivisorWeights.support S T)
      (lowerCoefficient S T l0 u0 l1 u1) n =
      SieveVector.lowerKernel (SieveDivisorWindow.evaluation S l0 n)
        (SieveDivisorWindow.evaluation S u0 n) (SieveDivisorWindow.evaluation T l1 n)
        (SieveDivisorWindow.evaluation T u1 n) := by
  unfold lowerCoefficient
  rw [evaluation_sub, evaluation_add,
    convolution_evaluation S T l0 u1 hc, convolution_evaluation S T u0 l1 hc,
    convolution_evaluation S T u0 u1 hc]
  rfl

theorem lowerCoefficient_reciprocal_mass (S T : Finset ℕ) (l0 u0 l1 u1 : ℕ → ℝ) :
    HarmanDivisorWindow.reciprocalMass (FactoredDivisorWeights.support S T)
      (lowerCoefficient S T l0 u0 l1 u1) =
      SieveVector.lowerKernel (HarmanDivisorWindow.reciprocalMass S l0)
        (HarmanDivisorWindow.reciprocalMass S u0) (HarmanDivisorWindow.reciprocalMass T l1)
        (HarmanDivisorWindow.reciprocalMass T u1) := by
  simp only [HarmanDivisorWindow.reciprocalMass, lowerCoefficient, add_div, sub_div,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  change HarmanDivisorWindow.reciprocalMass _ (FactoredDivisorWeights.coefficient S T l0 u1) +
    HarmanDivisorWindow.reciprocalMass _ (FactoredDivisorWeights.coefficient S T u0 l1) -
    HarmanDivisorWindow.reciprocalMass _ (FactoredDivisorWeights.coefficient S T u0 u1) = _
  rw [FactoredDivisorWeights.reciprocal_mass, FactoredDivisorWeights.reciprocal_mass,
    FactoredDivisorWeights.reciprocal_mass]
  rfl

#print axioms lowerCoefficient_abs_le_one
#print axioms lowerCoefficient_evaluation
run_cmd do
  for decl in [``collect_abs_le_one, ``coprime_product_injective, ``lowerCoefficient_eq_collect,
      ``lowerCoefficient_abs_le_one, ``upperCoefficient_abs_le_one, ``coprime_mul_dvd_iff,
      ``convolution_evaluation, ``evaluation_add, ``evaluation_sub,
      ``lowerCoefficient_evaluation, ``lowerCoefficient_reciprocal_mass] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
run_cmd Lean.logInfo "SIEVE_VECTOR_COLLECTION_PASSED; EXACT FINITE CONVOLUTION"

end SieveVectorCollection
end
