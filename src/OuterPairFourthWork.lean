import MaskedFourPrimeMeanWork
import OuterNormalizedModeWork

/-! Fourth moments of the actual correlated two-prime factor. Translations
are absorbed into unit coefficients; no independence of the mask is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace OuterPairFourthWork
open OuterModeUnitCapWork OuterNormalizedModeWork OuterSeparatedFourierModeWork
open DirichletPowerCoefficients Erdos374.HarmanAnalytic151MeanSquare
open Erdos374.HarmanGram152 MellinWindowFactor

theorem sum_four (A B : Finset ℕ) (f : (Fin 4→ℕ)→ℂ) :
    (∑z∈Fintype.piFinset ![A,B,A,B], f z) =
      ∑a∈A,∑b∈B,∑c∈A,∑d∈B, f ![a,b,c,d] := by
  symm
  calc
    _ = ∑z∈(A×ˢB)×ˢ(A×ˢB), f ![z.1.1,z.1.2,z.2.1,z.2.2] := by
      simp only [Finset.sum_product]
    _ = _ := ?_
  apply Finset.sum_bij (fun z _ => ![z.1.1,z.1.2,z.2.1,z.2.2])
  · intro z hz
    simp only [Finset.mem_product] at hz
    apply Fintype.mem_piFinset.mpr
    intro i
    fin_cases i <;> simp_all
  · intro z hz w hw he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    have h2 := congrFun he 2
    have h3 := congrFun he 3
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three] at h0 h1 h2 h3
    exact Prod.ext (Prod.ext h0 h1) (Prod.ext h2 h3)
  · intro z hz
    have hz' := Fintype.mem_piFinset.mp hz
    refine ⟨((z 0,z 1),(z 2,z 3)),?_,?_⟩
    · simpa using
        And.intro (And.intro (hz' 0) (hz' 1)) (And.intro (hz' 2) (hz' 3))
    · ext i; fin_cases i <;> rfl
  · intro z hz
    rfl

def weight (q : ℕ→ℕ→ℂ) (u v : ℝ) (z : Fin 4→ℕ) : ℂ :=
  q (z 0) (z 1)*q (z 2) (z 3)*
    logPhase u (z 0)*logPhase v (z 1)*logPhase u (z 2)*logPhase v (z 3)

theorem weight_cap (A B : Finset ℕ) (q : ℕ→ℕ→ℂ) (u v : ℝ)
    (hq : ∀a∈A,∀b∈B,‖q a b‖≤1) (z : Fin 4→ℕ)
    (hz : z∈Fintype.piFinset ![A,B,A,B]) : ‖weight q u v z‖≤1 := by
  have hm := Fintype.mem_piFinset.mp hz
  have h01 := hq (z 0) (by simpa using hm 0) (z 1) (by simpa using hm 1)
  have h23 := hq (z 2) (by simpa using hm 2) (z 3) (by simpa using hm 3)
  simpa only [weight,norm_mul,logPhase_norm,mul_one] using
    (mul_le_mul h01 h23 (norm_nonneg _) (by norm_num : (0:ℝ)≤1))

theorem square_expansion (A B : Finset ℕ) (q : ℕ→ℕ→ℂ) (σ t u v : ℝ)
    (hA : ∀a∈A,0<a) (hB : ∀b∈B,0<b) :
    pairPolynomial A B q σ (t-u) (t-v)^2 =
      ∑z∈Fintype.piFinset ![A,B,A,B],
        weight q u v z*(productIndex z:ℂ)^(-line σ t) := by
  rw [sum_four]
  unfold pairPolynomial verticalDirichlet152
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  have hp : productIndex ![a,b,c,d]=a*b*c*d := by
    simp [productIndex,Fin.prod_univ_succ]; ring
  rw [hp]
  simp only [nat_mul_cpow]
  have hs (n : ℕ) (hn : 0<n) (w : ℝ) :
      (n:ℂ)^(-((σ:ℂ)+Complex.I*((t-w:ℝ):ℂ))) =
        logPhase w n*(n:ℂ)^(-line σ t) := by
    simpa [line,mul_comm] using (phase_shift n hn σ t w).symm
  rw [hs a (hA a ha),hs b (hB b hb),hs c (hA c hc),hs d (hB d hd)]
  change _ = (q a b*q c d*logPhase u a*logPhase v b*logPhase u c*logPhase v d)*_
  ring

theorem fourth_expansion (A B : Finset ℕ) (q : ℕ→ℕ→ℂ) (σ t u v : ℝ)
    (hA : ∀a∈A,0<a) (hB : ∀b∈B,0<b) :
    ‖pairPolynomial A B q σ (t-u) (t-v)‖^4 =
      ‖∑z∈Fintype.piFinset ![A,B,A,B],
        (conj (weight q u v z)/(((productIndex z:ℝ)^σ:ℝ):ℂ))*
          exponentialKernel151 (Real.log (productIndex z)) t‖^2 := by
  rw [show (4:ℕ)=2*2 by norm_num, pow_mul, ←norm_pow,
    square_expansion A B q σ t u v hA hB]
  congr 1
  rw [←RCLike.norm_conj]
  congr 1
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hzp : 0<productIndex z := by
    apply Finset.prod_pos
    intro i _
    have hm := Fintype.mem_piFinset.mp hz i
    fin_cases i
    · exact hA _ hm
    · exact hB _ hm
    · exact hA _ hm
    · exact hB _ hm
  rw [line,cpow_vertical_factor152 hzp]
  simp only [map_mul,map_inv₀,Complex.conj_ofReal,conj_kernel152,neg_neg]
  ring

/-- Uniform in both translated frequencies and every correlated unit mask.
The length guard depends on the product of the two dyadic lengths. -/
theorem eventual_fourth_bound :
    ∃ W : ℝ, 2≤W ∧ ∀ (Na Nb : ℕ), W≤(Na:ℝ) → W≤(Nb:ℝ) →
      ∀ (A B : Finset ℕ) (q : ℕ→ℕ→ℂ) (a T σ ell u v : ℝ),
        0≤T → 1≤σ → 0<ell → ell≤Real.log Na → ell≤Real.log Nb →
        T≤(16*(Na*Nb)^2:ℕ) →
        (∀p∈A,p.Prime ∧ Na≤p ∧ p≤2*Na) →
        (∀p∈B,p.Prime ∧ Nb≤p ∧ p≤2*Nb) →
        (∀p∈A,∀r∈B,‖q p r‖≤1) →
        (∫t in Icc a (a+T),‖pairPolynomial A B q σ (t-u) (t-v)‖^4)≤
          FourPrimeMomentWork.momentConstant/ell^4 := by
  obtain ⟨W,hW,hm⟩ := MaskedFourPrimeMeanWork.eventual_block_bound
  refine ⟨W,hW,?_⟩
  intro Na Nb hNa hNb A B q a T σ ell u v hT hσ hell hla hlb hlen hA hB hq
  have hh := hm ![Na,Nb,Na,Nb]
    (by intro i; fin_cases i <;> assumption)
    ![A,B,A,B] (Fintype.piFinset ![A,B,A,B]) (fun z => conj (weight q u v z))
    a T σ ell hT hσ hell (by intro i; fin_cases i <;> assumption)
    (by convert hlen using 1; simp [Fin.prod_univ_succ]; ring)
    (by intro i; fin_cases i <;> assumption) (Finset.Subset.refl _) (by
      intro z hz
      simpa only [RCLike.norm_conj] using weight_cap A B q u v hq z hz)
  simp_rw [fourth_expansion A B q σ _ u v
    (fun p hp => (hA p hp).1.pos) (fun p hp => (hB p hp).1.pos)]
  exact hh

run_cmd do
  for decl in [``sum_four, ``weight_cap, ``square_expansion,
      ``fourth_expansion, ``eventual_fourth_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairFourthWork
