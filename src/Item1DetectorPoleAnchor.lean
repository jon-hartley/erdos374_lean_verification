import PrimeNumberTheoremAnd.ZetaBounds
import Item1EulerZeroDetector
import Item1ZeroFreeScaleClock

/-! Original-source integration. Both arithmetic inputs used here
are actual inspected declarations of PrimeNumberTheoremAnd.ZetaBounds:
riemannZetaLogDerivResidue and ZetaLowerBound3. Their original proof trees are
not independently replayed here. No shrinking-strip growth or left-of-one
nonvanishing premise is used by these pole and center estimates. -/
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
open Complex Set Filter Metric
open scoped Topology
namespace Item1DetectorPoleAnchor
open Item1EulerZeroDetector Item1ZeroFreeScaleClock

/-- A genuine small-positive-h pole bound, constructed from the retained
bounded regular part. h=0 is not included and no value at the pole is used. -/
theorem exists_pole_guard :
    ∃ eps : ℝ, 0<eps ∧ ∀ h : ℝ, 0<h → h<eps →
      (F ((1+h:ℝ):ℂ)).re≤17/(16*h) := by
  obtain ⟨U,hU,B,hB⟩ := riemannZetaLogDerivResidue
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  let C : ℝ := |B|+1
  have hC : 0<C := by dsimp [C]; positivity
  let eps : ℝ := min (r/2) (1/(16*C))
  refine ⟨eps,lt_min (by positivity) (by positivity),?_⟩
  intro h hh heps
  let z : ℂ := ((1+h:ℝ):ℂ)
  have hhr : h<r := by
    have hs := heps.trans_le (min_le_left (r/2) (1/(16*C)))
    linarith
  have hzU : z∈U := by
    apply hrU
    simpa [z,Metric.mem_ball,dist_eq_norm,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hh] using hhr
  have hz1 : z≠1 := by
    intro hz
    have hv := congrArg Complex.re hz
    simp [z] at hv
    linarith
  have hraw := hB (Set.mem_image_of_mem
    (norm ∘ (-(deriv riemannZeta / riemannZeta) - (fun s : ℂ => (s-1)⁻¹)))
    (show z∈U\{1} from ⟨hzU,by simpa using hz1⟩))
  have hnorm : ‖F z-((1/h:ℝ):ℂ)‖≤B := by
    simpa [Function.comp_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,
      F,z,neg_div,one_div] using hraw
  have hre : (F z).re-1/h≤B := by
    have he := Complex.re_le_norm (F z-((1/h:ℝ):ℂ))
    simp only [Complex.sub_re,Complex.ofReal_re] at he
    exact he.trans hnorm
  have hBsmall : B≤C := by dsimp [C]; linarith [le_abs_self B]
  have hch : C*h≤1/16 := by
    have hlim : h≤1/(16*C) :=
      heps.le.trans (min_le_right (r/2) (1/(16*C)))
    have hc' := (le_div_iff₀ (by positivity : 0<16*C)).mp hlim
    nlinarith
  have hClim : C≤1/(16*h) := by
    apply (le_div_iff₀ (by positivity : 0<16*h)).mpr
    nlinarith
  have hid : 1/h+1/(16*h)=17/(16*h) := by field_simp; ring
  have he : (F z).re≤1/h+1/(16*h) := by linarith
  exact he.trans_eq hid

/-- A deliberately coarse anchor, uniform in h and height, supplied by the
original right-of-one lower bound. No reciprocal Euler theorem is assumed. -/
theorem exists_moving_anchor :
    ∃ c : ℝ, 0<c ∧ ∀ h v : ℝ, 0<h → h≤1 → 4≤v →
      1≤Real.log v →
      c*h/Real.log v≤‖riemannZeta (((1+h:ℝ):ℂ)+(v:ℂ)*Complex.I)‖ := by
  obtain ⟨c,hc,hbound⟩ := ZetaLowerBound3
  refine ⟨c,hc,?_⟩
  intro h v hh hh1 hv hlog
  have hvp : 0<v := by linarith
  have hLp : 0<Real.log v := by linarith
  have hhpow : h≤h^(3/4:ℝ) := by
    have hlogh : Real.log h≤0 := Real.log_nonpos hh.le hh1
    rw [Real.rpow_def_of_pos hh]
    calc
      h = Real.exp (Real.log h) := (Real.exp_log hh).symm
      _ ≤ Real.exp (Real.log h*(3/4:ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have hLpow : (Real.log v)^(1/4:ℝ)≤Real.log v :=
    Real.rpow_le_self_of_one_le hlog (by norm_num)
  have hsmall := hbound (σ:=1+h) ⟨by linarith,by linarith⟩ v
    (by rw [abs_of_pos hvp]; linarith)
  have hsmall' : c*h^(3/4:ℝ)/(Real.log v)^(1/4:ℝ)≤
      ‖riemannZeta (((1+h:ℝ):ℂ)+(v:ℂ)*Complex.I)‖ := by
    simpa only [add_sub_cancel_left,abs_of_pos hvp] using hsmall
  calc
    c*h/Real.log v ≤ c*h/(Real.log v)^(1/4:ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg hc.le hh.le)
        (Real.rpow_pos_of_pos hLp _) hLpow
    _ ≤ c*h^(3/4:ℝ)/(Real.log v)^(1/4:ℝ) := by gcongr
    _ ≤ _ := hsmall'

/-- Scalar form used at the centers t and 2t. The parent lower-bound
constant is chosen once, before x, t, and either center. -/
theorem scaled_center_anchor (c x v : ℝ) (hc : 0<c) (hx : 1≤x)
    (hv : 4≤v) (hvlog : 1≤Real.log v) (hloghi : Real.log v≤2*x^12)
    (ha : ∀ h v : ℝ, 0<h → h≤1 → 4≤v → 1≤Real.log v →
      c*h/Real.log v≤‖riemannZeta (((1+h:ℝ):ℂ)+(v:ℂ)*Complex.I)‖) :
    c/(2*x^21)≤‖riemannZeta (((1+step x:ℝ):ℂ)+(v:ℂ)*Complex.I)‖ := by
  have hxp : 0<x := by linarith
  have hh : 0<step x := by unfold step; positivity
  have hh1 : step x≤1 := by
    unfold step
    exact (div_le_one (pow_pos hxp 9)).mpr (one_le_pow₀ hx)
  have hhi := ha (step x) v hh hh1 hv hvlog
  have hden := div_le_div_of_nonneg_left (mul_nonneg hc.le hh.le)
    (by linarith : 0<Real.log v) hloghi
  have he : c*step x/(2*x^12)=c/(2*x^21) := by
    unfold step
    field_simp [hxp.ne']
    <;> ring
  rw [he] at hden
  exact hden.trans hhi

#print axioms exists_pole_guard
#print axioms exists_moving_anchor
run_cmd do
  for target in [``exists_pole_guard, ``exists_moving_anchor, ``scaled_center_anchor] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Item1DetectorPoleAnchor
