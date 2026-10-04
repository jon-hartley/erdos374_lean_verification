import SourceLogMoment
import MangoldtReciprocal

/-! v6: Remove the reciprocal-mass premise from the logarithmic moment.
This uses the inherited elementary Mertens
bound, not PNT or a prime-polynomial cancellation premise. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SourceMassDischarge
open SourceMomentFinite SourceLogMoment
open Erdos374.HarmanGram152

def mangoldt (n : ℕ) : ℂ := ArithmeticFunction.vonMangoldt n

def restricted (S : Finset ℕ) (n : ℕ) : ℂ :=
  if n ∈ S then mangoldt n else 0

theorem interval_mass_identity (D N : ℕ) (hDN : D ≤ N) :
    (∑ n ∈ Finset.Ioc D N, MangoldtReciprocal.coefficient n) =
      MangoldtReciprocal.mass (N:ℝ)-MangoldtReciprocal.mass (D:ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Ioc 0 N) (fun n => n ≤ D) MangoldtReciprocal.coefficient
  have hleft : (Finset.Ioc 0 N).filter (fun n => n ≤ D) = Finset.Ioc 0 D := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  have hright : (Finset.Ioc 0 N).filter (fun n => ¬n ≤ D) = Finset.Ioc D N := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  rw [hleft,hright] at hsplit
  simp only [MangoldtReciprocal.mass,Nat.floor_natCast]
  linarith

/-- Uniform for every natural D>=1, not only eventually. -/
theorem full_interval_mass_le_fifteen (D : ℕ) (hD : 1 ≤ D) :
    (∑ n ∈ Finset.Ioc D (upper D),
      ArithmeticFunction.vonMangoldt n/(n:ℝ)) ≤ 15 := by
  have hDp : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hDr : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hNr : (1:ℝ) ≤ upper D := by exact_mod_cast hD.trans (upper_ge D)
  have hd := MangoldtReciprocal.mass_bounds (D:ℝ) hDr
  have hn := MangoldtReciprocal.mass_bounds (upper D:ℝ) hNr
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hid : Real.log (upper D:ℝ) = 6*Real.log 2+Real.log D := by
    simp only [upper,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [Real.log_mul (by positivity) hDp.ne',Real.log_pow]
    norm_num
  change (∑ n ∈ Finset.Ioc D (upper D), MangoldtReciprocal.coefficient n) ≤ 15
  rw [interval_mass_identity D (upper D) (upper_ge D)]
  linarith [hd.1,hn.2]

theorem dominated_mass (D : ℕ) (a : ℕ → ℂ) (hD : 1 ≤ D)
    (ha : ∀ n ∈ Finset.Ioc D (upper D),
      ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n) : mass D a ≤ 15 := by
  apply (Finset.sum_le_sum (fun n hn =>
    div_le_div_of_nonneg_right (ha n hn) (Nat.cast_nonneg n))).trans
  exact full_interval_mass_le_fifteen D hD

theorem restricted_majorant (S : Finset ℕ) (n : ℕ) :
    ‖restricted S n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n ∈ S
  · simp only [restricted,hn,ite_true,mangoldt,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,le_refl]
  · simp [restricted,hn,ArithmeticFunction.vonMangoldt_nonneg]

theorem restricted_polynomial (D : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc D (upper D)) (t : ℝ) :
    polynomial D (restricted S) t = verticalDirichlet152 S mangoldt 1 t := by
  unfold polynomial verticalDirichlet152
  -- Use congruence and finite support rather than any spectral estimate.
  calc
    _ = ∑ n ∈ S, restricted S n * (n:ℂ)^(-((1:ℂ)+Complex.I*(t:ℂ))) := by
      symm
      apply Finset.sum_subset hS
      intro n _ hn
      simp [restricted,hn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [restricted,hn]

def commonConstant : ℝ := ∑ h ∈ Finset.range 6, SourceLogMoment.momentConstant h

theorem momentConstant_nonneg (h : ℕ) : 0 ≤ SourceLogMoment.momentConstant h := by
  unfold SourceLogMoment.momentConstant SourceLogMoment.secondConstant
    SourceLogMoment.quadraticConstant SourceLogMoment.sexticConstant
    SourceLogMoment.energyConstant SourceLogMoment.cap SourceLogMoment.zeta
  positivity

theorem commonConstant_nonneg : 0 ≤ commonConstant :=
  Finset.sum_nonneg (fun h _ => momentConstant_nonneg h)

theorem momentConstant_le_common (h : ℕ) (hh : h ≤ 5) :
    SourceLogMoment.momentConstant h ≤ commonConstant := by
  exact Finset.single_le_sum (fun k _ => momentConstant_nonneg k)
    (Finset.mem_range.mpr (by omega))

/-- The mass hypothesis in v5 has been discharged. No cancellation input is
used. The remaining hypotheses specify the actual support and length guard. -/
theorem supported_moment (D h : ℕ) (S : Finset ℕ) (X a0 T β : ℝ)
    (hD : 1 ≤ D) (hh : 2 ≤ h) (hh5 : h ≤ 5)
    (hX : 2 ≤ X) (hDX : (D:ℝ) ≤ X) (hT : 1 ≤ T) (hTX : T ≤ 2*X)
    (hβ0 : 2*(h:ℝ) ≤ β) (hβ1 : β ≤ 3*(h:ℝ))
    (hS : S ⊆ Finset.Ioc D (upper D))
    (hlen : T^4 ≤ (D:ℝ)^(β+2*(h:ℝ))) :
    (∫ t in Icc a0 (a0+T), ‖verticalDirichlet152 S mangoldt 1 t‖^β) ≤
      commonConstant*(1+Real.log X)^18 := by
  have hhr : (0:ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hp0 : 2 ≤ β/(h:ℝ) := (le_div_iff₀ hhr).mpr hβ0
  have hp1 : β/(h:ℝ) ≤ 3 := (div_le_iff₀ hhr).mpr hβ1
  have horder : (h:ℝ)*(β/(h:ℝ)) = β := by field_simp
  have hlength : T^4 ≤ (((D^h:ℕ):ℝ))^(β/(h:ℝ)+2) := by
    rw [Nat.cast_pow,←Real.rpow_natCast_mul (Nat.cast_nonneg D)]
    convert hlen using 1
    congr 1
    field_simp
  have hm := SourceLogMoment.source_order_moment D h (restricted S) X a0 T (β/(h:ℝ))
    hD hh hh5 hX hDX hT hTX hp0 hp1
    (fun n _ => restricted_majorant S n)
    ((dominated_mass D (restricted S) hD (fun n _ => restricted_majorant S n)).trans
      (by norm_num : (15:ℝ) ≤ 64)) hlength
  simp_rw [restricted_polynomial D S hS,horder] at hm
  exact hm.trans (mul_le_mul_of_nonneg_right (momentConstant_le_common h hh5)
    (by positivity))

#print axioms supported_moment
run_cmd do
  for n in [``interval_mass_identity,``full_interval_mass_le_fifteen,``dominated_mass,
      ``restricted_majorant,``restricted_polynomial,``momentConstant_nonneg,
      ``commonConstant_nonneg,``momentConstant_le_common,``supported_moment] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "SOURCE MASS DISCHARGED: VALID ONLY AFTER SUCCESSFUL COMPILATION"
end SourceMassDischarge
