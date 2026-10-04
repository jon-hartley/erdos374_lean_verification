import Item1ParameterCore

/-! The complete product of the explicit coordinate factors contributes
exactly the logarithmic terms used in rawLoss. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace Item1ParameterFactorProduct
open Item1ParameterCore

theorem sum_degree_indices (d : ℕ) :
    (∑ j : Fin d, ((j.val+1:ℕ):ℝ)) = (d:ℝ)*((d:ℝ)+1)/2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ j : Fin d, ((j.val+1:ℕ):ℝ)) + ((d+1:ℕ):ℝ) = _
    rw [ih]
    push_cast
    ring

theorem logFactor_pos (d j : ℕ) (m : ℝ) (hd : 1 ≤ d) (hm : 0 ≤ m) :
    0 < logFactor d j m := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log (8*(d:ℝ)^2) := Real.log_nonneg (by nlinarith)
  unfold logFactor
  positivity

theorem logFactor_le (d j : ℕ) (m : ℝ) (hjd : j ≤ d) (hm : 0 ≤ m) :
    logFactor d j m ≤ logFactor d d m := by
  unfold logFactor
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (show (j:ℝ) ≤ d by exact_mod_cast hjd) hm)

theorem factor_pos (d j : ℕ) (m : ℝ) (hd : 1 ≤ d) (hj : 1 ≤ j) (hm : 0 ≤ m) :
    0 < factor d j m := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hjpos : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hlf := logFactor_pos d j m hd hm
  unfold factor
  positivity

theorem log_factor_le (d j : ℕ) (m : ℝ)
    (hd : 1 ≤ d) (hj : 1 ≤ j) (hjd : j ≤ d) (hm : 0 ≤ m) :
    Real.log (factor d j m) ≤
      Real.log 1600 + 5*Real.log (d:ℝ) + (j:ℝ)*Real.log 2 +
        Real.log (logFactor d d m) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hjpos : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hlf := logFactor_pos d j m hd hm
  have hlogj := Real.log_le_log hjpos (show (j:ℝ) ≤ d by exact_mod_cast hjd)
  have hloglf := Real.log_le_log hlf (logFactor_le d j m hjd hm)
  unfold factor
  rw [Real.log_mul (by positivity) hlf.ne',
    Real.log_mul (by positivity) (pow_ne_zero j (by norm_num)),
    Real.log_mul (by positivity) hjpos.ne',
    Real.log_mul (by norm_num) (pow_ne_zero 4 hdpos.ne'),
    Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [hlogj, hloglf]

/-- Uniformly replacing the coordinate logarithms by their value at d
gives the exact expanded logarithmic loss used by the later absorption. -/
theorem factor_product_le_exp (d : ℕ) (m : ℝ) (hd : 1 ≤ d) (hm : 0 ≤ m) :
    (∏ j : Fin d, factor d (j.val+1) m) ≤
      Real.exp ((d:ℝ)*Real.log 1600 + 5*(d:ℝ)*Real.log (d:ℝ) +
        (1/2:ℝ)*(d:ℝ)*((d:ℝ)+1)*Real.log 2 +
        (d:ℝ)*Real.log (logFactor d d m)) := by
  have hpos : ∀ j : Fin d, 0 < factor d (j.val+1) m :=
    fun j => factor_pos d (j.val+1) m hd (by omega) hm
  have hprod : 0 < ∏ j : Fin d, factor d (j.val+1) m :=
    Finset.prod_pos (fun j _ => hpos j)
  apply (Real.log_le_log_iff hprod (Real.exp_pos _)).mp
  rw [Real.log_exp, Real.log_prod (fun j _ => (hpos j).ne')]
  calc
    (∑ j : Fin d, Real.log (factor d (j.val+1) m)) ≤
        ∑ j : Fin d, (Real.log 1600 + 5*Real.log (d:ℝ) +
          ((j.val+1:ℕ):ℝ)*Real.log 2 + Real.log (logFactor d d m)) := by
      apply Finset.sum_le_sum
      intro j _
      exact log_factor_le d (j.val+1) m hd (by omega) (by omega) hm
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, sum_degree_indices]
      ring

end Item1ParameterFactorProduct

run_cmd do
  for target in [``Item1ParameterFactorProduct.sum_degree_indices,
      ``Item1ParameterFactorProduct.logFactor_pos,
      ``Item1ParameterFactorProduct.logFactor_le,
      ``Item1ParameterFactorProduct.factor_pos,
      ``Item1ParameterFactorProduct.log_factor_le,
      ``Item1ParameterFactorProduct.factor_product_le_exp] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "PARAMETER FACTOR PRODUCT: 6 standard-axiom theorem guards passed."
