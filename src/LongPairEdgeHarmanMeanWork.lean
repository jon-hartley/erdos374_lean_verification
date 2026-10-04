import FactoredDivisorMeanSquare
import CofactorDoublingCoverage
import PositiveSharpPowerWindow

/-! A genuine enlargement of the available product range, conditional only
on explicit factor lengths: total product up to X^.772, selected factor
up to X^.229. This is an analytic building block, not full sector coverage. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace LongPairEdgeHarmanMeanWork
open MellinCofactorCoverage FactoredDivisorWeights PositiveSharpPowerWindow HarmanDivisorWindow

theorem numeric_guards (X : ℝ) (M N lo : ℕ)
    (hX : 1≤X) (hM : 1≤M) (hN : 1≤N)
    (hlo : X/(32*((M*N:ℕ):ℝ))≤(lo:ℝ))
    (h32 : 32≤X^(1/10000:ℝ)) (hNcap : (N:ℝ)≤X^(229/1000:ℝ)) :
    X^((1/20000:ℝ)/10)*(X^(8992/10000:ℝ))^(10/9:ℝ)≤(lo*M*N:ℕ) ∧
    X^(1/20000:ℝ)*(X^(8992/10000:ℝ))^(6/7:ℝ)≤
      max (lo*M:ℕ) (M*N:ℕ) := by
  have hXp : 0<X := by linarith
  have hMp : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hprod : X≤32*(lo:ℝ)*((M*N:ℕ):ℝ) := by
    have hh := (div_le_iff₀ (by positivity : 0<32*((M*N:ℕ):ℝ))).mp hlo
    nlinarith
  have hmargin : 32*X^(9999/10000:ℝ)≤X := by
    calc
      _ ≤ X^(1/10000:ℝ)*X^(9999/10000:ℝ) :=
        mul_le_mul_of_nonneg_right h32 (by positivity)
      _ = X := by rw [←Real.rpow_add hXp]; norm_num
  have htotal : X^(9999/10000:ℝ)≤(lo:ℝ)*((M*N:ℕ):ℝ) := by nlinarith
  have hpair : X^(7709/10000:ℝ)≤((lo*M:ℕ):ℝ) := by
    have hupper : (lo:ℝ)*((M*N:ℕ):ℝ)≤((lo*M:ℕ):ℝ)*X^(229/1000:ℝ) := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hNcap
        (mul_nonneg (Nat.cast_nonneg lo) hMp.le)]
    have he : X^(9999/10000:ℝ)=X^(7709/10000:ℝ)*X^(229/1000:ℝ) := by
      rw [←Real.rpow_add hXp]; norm_num
    rw [he] at htotal
    nlinarith [Real.rpow_pos_of_pos hXp (229/1000:ℝ)]
  constructor
  · rw [←Real.rpow_mul hXp.le, ←Real.rpow_add hXp]
    apply (Real.rpow_le_rpow_of_exponent_le hX (by norm_num :
      (1/20000:ℝ)/10+(8992/10000)*(10/9)≤9999/10000)).trans
    simpa only [Nat.cast_mul, mul_assoc] using htotal
  · rw [←Real.rpow_mul hXp.le, ←Real.rpow_add hXp]
    apply (Real.rpow_le_rpow_of_exponent_le hX (by norm_num :
      (1/20000:ℝ)+(8992/10000)*(6/7)≤7709/10000)).trans
    exact hpair.trans (by exact_mod_cast (le_max_left (lo*M) (M*N)))

/-- Unit real factor weights at the actual .101 half-width. The upper
selected-factor exponent .229 is strictly larger than 8/35. -/
theorem eventually_bound :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℝ in atTop, Real.exp 1≤X ∧
      ∀ (M N : ℕ) (sm sn : Finset ℕ) (am an : ℕ → ℝ),
        let A : ℝ := (M*N:ℕ)
        let Y := halfWidth X (101/1000)
        1≤M → 1≤N → X^(1/2:ℝ)≤A → A≤X^(772/1000:ℝ) →
        X^(1/5:ℝ)≤(N:ℝ) → (N:ℝ)≤X^(229/1000:ℝ) →
        (∀ n∈sm,M<n ∧ n≤2*M) → (∀ n∈sn,N<n ∧ n≤2*N) →
        (∀ n∈sm,|am n|≤1) → (∀ n∈sn,|an n|≤1) →
        (1/X)*(∫ x in Icc X (2*X), remainder (support sm sn)
          (coefficient sm sn am an) (x-x*(Y/X)) x ^ 2)≤Y^2*X^(-c) := by
  obtain ⟨c,hc,hm⟩ := FactoredDivisorMeanSquare.eventually_bound
    (1009/10000) (227/1000) (1/5) (1/20000) (1/1000) (1/1000) (1/20000) 9
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
  refine ⟨c,hc,?_⟩
  filter_upwards [hm, CofactorDoublingCoverage.eventual_scales
      (1/2) (227/1000) (1/1000) (by norm_num) (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_constant_bound 32 (1/10000) (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_constant_bound 2 (1/10000) (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_constant_bound 2 (8982/10000) (by norm_num) (by norm_num),
    halfWidth_eventually (101/1000) (by norm_num)] with X hmean hcov h32 h2 hUlow hY
  refine ⟨hmean.1,?_⟩
  intro M N sm sn am an
  dsimp only
  intro hM hN hAlow hAhigh hNlow hNhigh hsm hsn ham han
  have hX : 1≤X := h32.1
  have hXp : 0<X := by linarith
  let A : ℝ := ((M*N:ℕ):ℝ)
  let lo := lowerCutoff X A
  have hAp : 0<A := by dsimp [A]; push_cast; positivity
  have hAupper : A≤X^(1-(227/1000:ℝ)-1/1000) := by
    convert hAhigh using 1; norm_num [A]
  obtain ⟨hlower, _hone, hhi, hscale⟩ := hcov.2 A hAlow hAupper
  have hAX : A≤X := hAhigh.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
      (by norm_num : (772/1000:ℝ)≤1))
  have hscale32 : 32*A≤X := by
    have hh : 32*A≤X^(1/10000:ℝ)*X^(772/1000:ℝ) :=
      mul_le_mul h32.2 hAhigh hAp.le (by positivity)
    apply hh.trans
    rw [←Real.rpow_add hXp]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
      (by norm_num : (1/10000:ℝ)+772/1000≤1)
  have hlo : X/(32*A)≤(lo:ℝ) := lowerCutoff_scale X A hAp hscale32
  obtain ⟨hproduct,hpair⟩ := numeric_guards X M N lo hX hM hN hlo h32.2 hNhigh
  have hHroot : X^(1/1000:ℝ)≤(lo:ℝ)^(1/4:ℝ) := by
    have hh := Real.rpow_le_rpow (by positivity : 0≤X^(227/1000:ℝ)) hlower
      (by norm_num : (0:ℝ)≤1/4)
    rw [←Real.rpow_mul hXp.le] at hh
    exact (Real.rpow_le_rpow_of_exponent_le hX (by norm_num :
      (1/1000:ℝ)≤(227/1000)*(1/4))).trans hh
  have hU : 2*X^(1/1000:ℝ)≤X^(8992/10000:ℝ) := by
    calc
      _ ≤ X^(8982/10000:ℝ)*X^(1/1000:ℝ) :=
        mul_le_mul_of_nonneg_right hUlow.2 (by positivity)
      _ = _ := by rw [←Real.rpow_add hXp]; norm_num
  have hYlower : X^(1009/10000:ℝ)≤halfWidth X (101/1000) := by
    unfold halfWidth
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    calc
      _ ≤ X^(1009/10000:ℝ)*X^(1/10000:ℝ) :=
        mul_le_mul_of_nonneg_left h2.2 (by positivity)
      _ = _ := by rw [←Real.rpow_add hXp]; norm_num
  apply hmean.2 M N sm sn am an (halfWidth X (101/1000))
    (X^(1/1000:ℝ)) (X^(8992/10000:ℝ)) hM hN hAX hlower hhi hscale hNlow
    hproduct hpair le_rfl hHroot
  · nlinarith [Real.rpow_nonneg hXp.le (1/1000:ℝ)]
  · exact hU
  · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
      (by norm_num : (8992/10000:ℝ)≤1)
  · exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num :
      (1:ℝ)-1009/10000+1/20000≤8992/10000)
  · exact hYlower
  · linarith [hY.2]
  · exact hsm
  · exact hsn
  · exact ham
  · exact han

#print axioms eventually_bound
run_cmd do
  for decl in [``numeric_guards, ``eventually_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairEdgeHarmanMeanWork
