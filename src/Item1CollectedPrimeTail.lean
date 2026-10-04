import Item1SharpTail
import Item1PrimeTripleFibers

/-! UNCOMPILED. Constructed finite coefficients, their exact pushforward mass,
and the full sharp prime tail. S is a finite set of ORDERED prime triples.
No representative is chosen in place of a product fiber. The only quantitative
arguments are elementary support, weight and reciprocal-mass inequalities.
The maintained source-cell constructor must still be matched to S in the project.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Item1CollectedPrimeTail
open Item1PrimeTripleFibers Item1FinitePolynomialTail Item1SharpTail Item1CountableTail

def products (S : Finset Triple) : Finset ℕ := S.image product

def rawCoeff (S : Finset Triple) (w : Triple → ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ S.filter (fun a => product a=n), w a

def coeff (S : Finset Triple) (w : Triple → ℝ) (n : ℕ) : ℝ := rawCoeff S w n/(n:ℝ)

def literal (S : Finset Triple) (w : Triple → ℝ) (t : ℝ) : ℂ :=
  ∑ a ∈ S, ((w a/(product a:ℝ)):ℂ) *
    Erdos374.HarmanAnalytic151MeanSquare.exponentialKernel151 (Real.log (product a)) (-t)

theorem rawCoeff_nonneg (S : Finset Triple) (w : Triple → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (n : ℕ) : 0 ≤ rawCoeff S w n :=
  Finset.sum_nonneg (fun a ha => hw a (Finset.mem_filter.mp ha).1)

theorem rawCoeff_le (S : Finset Triple) (w : Triple → ℝ) (ell : ℝ)
    (hl : 0 ≤ ell) (hp : ∀ a ∈ S, allPrime a)
    (hw : ∀ a ∈ S, w a ≤ ell^3) (n : ℕ) : rawCoeff S w n ≤ 6*ell^3 := by
  apply fiber_weight_le (S.filter (fun a => product a=n)) n ell w hl
  · intro a ha; exact hp a (Finset.mem_filter.mp ha).1
  · intro a ha; exact (Finset.mem_filter.mp ha).2
  · intro a ha; exact hw a (Finset.mem_filter.mp ha).1

/-- Exact finite pushforward identity; collisions are retained in rawCoeff. -/
theorem mass_identity (S : Finset Triple) (w : Triple → ℝ) :
    (∑ n ∈ products S, coeff S w n) = ∑ a ∈ S, w a/(product a:ℝ) := by
  classical
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := products S) (g := product)
    (fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩)
    (fun a => w a/(product a:ℝ))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro n hn
  unfold coeff rawCoeff
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

theorem literal_eq_collected (S : Finset Triple) (w : Triple → ℝ) (t : ℝ) :
    literal S w t = polynomial (products S) (coeff S w) t := by
  classical
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := products S) (g := product)
    (fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩)
    (fun a => ((w a/(product a:ℝ)):ℂ)*
      Erdos374.HarmanAnalytic151MeanSquare.exponentialKernel151 (Real.log (product a)) (-t))
  unfold literal polynomial Erdos374.HarmanAnalytic151MeanSquare.exponentialSum151
  rw [← hf]
  apply Finset.sum_congr rfl
  intro n hn
  unfold coeff rawCoeff
  simp only [Finset.sum_div, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]
  rw [Complex.ofReal_div]

theorem energy_bound (S : Finset Triple) (w : Triple → ℝ) (X ell : ℝ)
    (hX : 0 < X) (hl : 0 ≤ ell) (hp : ∀ a ∈ S, allPrime a)
    (hs : ∀ a ∈ S, X/8 ≤ (product a:ℝ))
    (hw0 : ∀ a ∈ S, 0 ≤ w a) (hw : ∀ a ∈ S, w a ≤ ell^3)
    (hm : (∑ a ∈ S, w a/(product a:ℝ)) ≤ 32*ell^3) :
    energy (products S) (coeff S w) ≤ 1536*ell^6/X := by
  apply coefficient_energy_le (products S) X ell (rawCoeff S w) hX hl
  · intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    exact hs a ha
  · intro n _; exact rawCoeff_nonneg S w hw0 n
  · intro n _; exact rawCoeff_le S w ell hl hp hw n
  · exact (mass_identity S w).le.trans hm

theorem rowCost_nonneg (N : ℕ) : 0 ≤ rowCost N := by
  by_cases hN : N=0
  · simp [rowCost,hN]
  · have h1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
    have hlog : 0 ≤ Real.log N := Real.log_nonneg h1
    unfold rowCost
    positivity

/-- Full prime tail with constructed coefficients. No frequency estimate occurs
among the hypotheses. The support and mass conditions are finite source data. -/
theorem prime_sharp_tail (S : Finset Triple) (w : Triple → ℝ) (N : ℕ)
    (X ell eta H : ℝ) (hX : 0 < X) (hl : 0 ≤ ell)
    (he0 : 0 < eta) (he1 : eta ≤ 1/2) (hH : 1 ≤ H)
    (hp : ∀ a ∈ S, allPrime a)
    (hsN : ∀ a ∈ S, 1 ≤ product a ∧ product a ≤ N)
    (hsX : ∀ a ∈ S, X/8 ≤ (product a:ℝ))
    (hw0 : ∀ a ∈ S, 0 ≤ w a) (hw : ∀ a ∈ S, w a ≤ ell^3)
    (hm : (∑ a ∈ S, w a/(product a:ℝ)) ≤ 32*ell^3) :
    (∫ t in outside H, ‖multiplier eta t*literal S w t‖^2) ≤
      24576*ell^6/(eta^2*X*H)+49152*rowCost N*ell^6/(3*eta^2*X*H^2) := by
  have hs : ∀ n ∈ products S, 1 ≤ n ∧ n ≤ N := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    exact hsN a ha
  have hb := polynomial_sharp_tail (products S) (coeff S w) N hs eta H he0 he1 hH
  have he := energy_bound S w X ell hX hl hp hsX hw0 hw hm
  have hrow := rowCost_nonneg N
  have hfactor : 0 ≤ 16/(eta^2*H)+32*rowCost N/(3*eta^2*H^2) := by positivity
  have hh := mul_le_mul_of_nonneg_left he hfactor
  simp_rw [literal_eq_collected]
  calc
    _ ≤ 16*energy (products S) (coeff S w)/(eta^2*H)+
        32*rowCost N*energy (products S) (coeff S w)/(3*eta^2*H^2) := hb
    _ = (16/(eta^2*H)+32*rowCost N/(3*eta^2*H^2))*
        energy (products S) (coeff S w) := by ring
    _ ≤ (16/(eta^2*H)+32*rowCost N/(3*eta^2*H^2))*(1536*ell^6/X) := hh
    _ = _ := by ring

end Item1CollectedPrimeTail

-- ROOT SOURCE RECURSIVE AUDIT: exact original declarations.
run_cmd do
  for target in [
    ``Item1CollectedPrimeTail.rawCoeff_nonneg,
    ``Item1CollectedPrimeTail.rawCoeff_le,
    ``Item1CollectedPrimeTail.mass_identity,
    ``Item1CollectedPrimeTail.literal_eq_collected,
    ``Item1CollectedPrimeTail.energy_bound,
    ``Item1CollectedPrimeTail.rowCost_nonneg,
    ``Item1CollectedPrimeTail.prime_sharp_tail] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1CollectedPrimeTail: 7 original theorem guards passed."
