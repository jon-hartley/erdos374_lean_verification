import Item1ZetaElementaryDisk
import Item1PositiveStripDefinitions
import Item1ZeroFreeDisk

/-!
Source integration. Derive the parent's quantitative/differentiable
PositiveStrip from bare zeta nonvanishing. No logarithmic-derivative or
polynomial-cap bound is accepted as a new parameter. BarePositiveZeroFree
remains unproved. Original elementary ZetaBounds dependencies remain required.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Set Metric Complex
namespace Item1ZeroFreeToStrip
open Item1ZeroFreeDisk Item1ZetaDiskGeometry Item1ZetaElementaryDisk
open Item1ZetaContourGeometry Item1RampDirichlet

/-- Pure nonvanishing implies the old positive-strip contract on a smaller
strip. All constants and the new threshold are chosen before sigma and y. -/
theorem positiveStrip_of_bare_zero_free (b T₀ : ℝ)
    (hb : 0<b) (hb1 : b≤1/2) (hT : 4≤T₀)
    (hzero : BarePositiveZeroFree b T₀) :
    ∃ T₁ : ℝ, 4≤T₁ ∧ PositiveStrip (b/8) (3072/b^2) T₁ := by
  obtain ⟨c,hc,hanchor⟩ := exists_coarse_anchor
  let T₁ : ℝ := max (max 64 (Real.exp 2)) (max (2*T₀) (16/c))
  have h64 : (64:ℝ)≤T₁ := (le_max_left _ _).trans (le_max_left _ _)
  have he2 : Real.exp 2≤T₁ := (le_max_right _ _).trans (le_max_left _ _)
  have h2T : 2*T₀≤T₁ := (le_max_left _ _).trans (le_max_right _ _)
  have hcT : 16/c≤T₁ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T₁,by linarith,?_⟩
  intro σ y hy hσ hσ1
  have hy64 : (64:ℝ)≤y := h64.trans hy
  have hyp : 0<y := by linarith
  have hL : 1≤Real.log y := by
    have hh := Real.log_le_log (Real.exp_pos 2) (he2.trans hy)
    rw [Real.log_exp] at hh
    linarith
  obtain ⟨hd,hd1⟩ := depth_guards b y hb hb1 hL
  have hdepth : depth b y=(b/8)/(Real.log y)^(3/4:ℝ) := by
    unfold depth; ring
  have hσ' : 1-depth b y≤σ := by simpa only [hdepth] using hσ
  let z : ℂ := (σ:ℂ)+(y:ℂ)*Complex.I
  have hz : ‖z-center y‖≤1+depth b y := target_inner b y σ hσ' hσ1
  have hzball : z∈ball (center y) (1+2*depth b y) := by
    rw [mem_ball,dist_eq_norm]
    linarith
  have hf := zeta_differentiable_disk y (depth b y) (by linarith) hd1
  have hn := disk_nonvanishing b T₀ y hb hb1 hT (by linarith)
    (h2T.trans hy) hL hzero
  have hratio := relative_disk_growth c b y hc (by linarith) hL
    (hcT.trans hy) hd1 (hanchor y (by linarith) hL)
  have hbound := logarithmic_derivative_disk riemannZeta (center y) z
    (depth b y) (3*Real.log y) hd hd1 (by linarith) hf hn hratio hz
  have hdiff := (logDerivative_differentiableOn riemannZeta (center y)
    (1+2*depth b y) hf hn).differentiableAt (isOpen_ball.mem_nhds hzball)
  constructor
  · change DifferentiableAt ℂ (fun w => -deriv riemannZeta w/riemannZeta w) z
    have hneg : DifferentiableAt ℂ
        (fun w => -(deriv riemannZeta w/riemannZeta w)) z := hdiff.neg
    simpa only [neg_div] using hneg
  · have hnorm : ‖zetaLogDeriv z‖=‖deriv riemannZeta z/riemannZeta z‖ := by
      simp only [zetaLogDeriv,neg_div,norm_neg]
    change ‖zetaLogDeriv z‖≤_
    rw [hnorm]
    exact hbound.trans (depth_budget b y hb hL)

end Item1ZeroFreeToStrip

run_cmd do
  for ax in (← Lean.collectAxioms ``Item1ZeroFreeToStrip.positiveStrip_of_bare_zero_free) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in Item1ZeroFreeToStrip.positiveStrip_of_bare_zero_free"

#print axioms Item1ZeroFreeToStrip.positiveStrip_of_bare_zero_free
