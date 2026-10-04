import OuterExceptionalFlatWork
import FlatCofactorApproximation
import ContinuousCofactorMellin

/-! Discrete-minus-continuous cofactor estimates. Centering does not
make the zero frequency identically zero; Euler summation controls its
entire low physical frequency neighborhood. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Set
namespace OuterCenteredFlatWork
open Erdos374.HarmanGram152 MellinWindowFactor

def continuousFlat (lo hi : ℕ) (σ t : ℝ) : ℂ :=
  ((hi:ℂ)^(1-line σ t)-(lo:ℂ)^(1-line σ t))/(1-line σ t)

def centeredFlat (lo hi : ℕ) (σ t : ℝ) : ℂ :=
  verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t -
    continuousFlat lo hi σ t

theorem continuousFlat_eq_integral (lo hi : ℕ) (σ t : ℝ)
    (hlo : 0<lo) (hhi : lo≤hi) (hσ : 1<σ) :
    continuousFlat lo hi σ t =
      ContinuousCofactorMellin.cofactor lo hi (line σ t) := by
  symm
  simpa [continuousFlat] using ContinuousCofactorMellin.cofactor_quotient
    lo hi σ t (by exact_mod_cast hlo) (by exact_mod_cast hhi) hσ

theorem continuousFlat_bound (lo hi : ℕ) (σ t : ℝ)
    (hlo : 1≤lo) (hhi : 1≤hi) (hσ : 1≤σ) (ht : 0 < |t|) :
    ‖continuousFlat lo hi σ t‖ ≤ 2/|t| := by
  have hp (n : ℕ) (hn : 1≤n) : ‖(n:ℂ)^(1-line σ t)‖≤1 := by
    have hnR : (1:ℝ)≤n := by exact_mod_cast hn
    rw [←Complex.ofReal_natCast n,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    have he : (1-line σ t).re=1-σ := by simp [line]
    rw [he]
    exact Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith)
  have hd : |t|≤‖1-line σ t‖ := by
    have hh := Complex.abs_im_le_norm (1-line σ t)
    simpa [line] using hh
  have hn : ‖(hi:ℂ)^(1-line σ t)-(lo:ℂ)^(1-line σ t)‖≤2 :=
    (norm_sub_le _ _).trans (by linarith [hp hi hhi,hp lo hlo])
  rw [continuousFlat,norm_div]
  exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by norm_num) ht hd)

theorem centeredFlat_euler (N lo hi : ℕ) (σ t : ℝ)
    (hN : 1≤N) (hlo : N≤lo) (hhi : lo<hi) (hσ : 1<σ) (hσ2 : σ≤2) :
    ‖centeredFlat lo hi σ t‖≤(3+|t|)/(N:ℝ) := by
  exact FlatCofactorApproximation.bound_any_upper N lo hi σ t hN hlo hhi hσ hσ2

theorem low_pointwise (X ε ρ : ℝ) (hX : 1≤X) (hρ : 0≤ρ)
    (N lo hi : ℕ) (σ t : ℝ) (hN : 1≤N)
    (hscale : X^ε≤(N:ℝ)) (hlo : N≤lo) (hhi : lo<hi)
    (hσ : 1<σ) (hσ2 : σ≤2) (ht : |t|≤X^ρ) :
    ‖centeredFlat lo hi σ t‖≤4*X^(ρ-ε) := by
  have hx : 0<X := by linarith
  have hpow : 1≤X^ρ := Real.one_le_rpow hX hρ
  apply (centeredFlat_euler N lo hi σ t hN hlo hhi hσ hσ2).trans
  calc
    (3+|t|)/(N:ℝ) ≤ (4*X^ρ)/(N:ℝ) :=
      div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    _ ≤ (4*X^ρ)/(X^ε) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hscale
    _ = 4*X^(ρ-ε) := by rw [Real.rpow_sub hx]; ring

theorem low_energy (X ε ρ : ℝ) (hX : 1≤X) (hρ : 0≤ρ)
    (N lo hi : ℕ) (σ : ℝ) (F : ℝ→ℂ) (hN : 1≤N)
    (hscale : X^ε≤(N:ℝ)) (hlo : N≤lo) (hhi : lo<hi)
    (hσ : 1<σ) (hσ2 : σ≤2)
    (hF : ∀t∈Icc (-(X^ρ)) (X^ρ), ‖F t‖≤1) :
    (∫t in Icc (-(X^ρ)) (X^ρ), ‖F t*centeredFlat lo hi σ t‖^2)
      ≤32*X^(3*ρ-2*ε) := by
  have hx : 0<X := by linarith
  have hpoint (t : ℝ) (ht : t∈Icc (-(X^ρ)) (X^ρ)) :
      ‖‖F t*centeredFlat lo hi σ t‖^2‖ ≤ (4*X^(ρ-ε))^2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hF t ht) (norm_nonneg _)).trans
      (by simpa using (low_pointwise X ε ρ hX hρ N lo hi σ t hN hscale
        hlo hhi hσ hσ2 (abs_le.mpr ht)))
  have hh := norm_setIntegral_le_of_norm_le_const (μ := volume)
    isCompact_Icc.measure_lt_top hpoint
  have hp : (X^(ρ-ε))^2=X^(2*(ρ-ε)) := by
    rw [←Real.rpow_mul_natCast hx.le]
    congr 1
    ring
  calc
    _ ≤ ‖∫t in Icc (-(X^ρ)) (X^ρ), ‖F t*centeredFlat lo hi σ t‖^2‖ := le_abs_self _
    _ ≤ (4*X^(ρ-ε))^2*volume.real (Icc (-(X^ρ)) (X^ρ)) := hh
    _ = 32*X^(3*ρ-2*ε) := by
      rw [Real.volume_real_Icc_of_le (by have := Real.rpow_nonneg hx.le ρ; linarith),
        mul_pow,hp]
      have he : X^(2*(ρ-ε))*X^ρ=X^(3*ρ-2*ε) := by
        rw [←Real.rpow_add hx]
        congr 1
        ring
      nlinarith [he]

run_cmd do
  for decl in [``continuousFlat_eq_integral, ``continuousFlat_bound,
      ``centeredFlat_euler, ``low_pointwise, ``low_energy] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
end OuterCenteredFlatWork
