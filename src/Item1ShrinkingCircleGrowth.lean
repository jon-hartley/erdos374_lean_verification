import Item1DetectorPoleAnchor
import Item1ZetaDetectorDefinitions

/-! Original-circle relative growth from a stated zeta modulus
bound. LogarithmicZetaGrowth is NOT proved here. The local geometry, center
anchor, and relative-growth conversion are supplied by proof bodies. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Set Metric Complex Filter
namespace Item1ShrinkingCircleGrowth
open Item1ZeroFreeScaleClock Item1DetectorPoleAnchor Item1AutomaticZetaDetector

/-- The genuine remaining analytic estimate, with a fixed natural log power.
It is not a nonvanishing or source-mean proposition. No proof is declared here. -/
def LogarithmicZetaGrowth (A : ℕ) (C Tg : ℝ) : Prop :=
  ∀ u v : ℝ, Tg≤v →
    1-1/(Real.log v)^(2/3:ℝ)≤u → u≤2 →
    ‖riemannZeta ((u:ℂ)+(v:ℂ)*Complex.I)‖≤C*(Real.log v)^A

theorem nearby_log_bounds (t x v : ℝ) (ht : 9≤t)
    (htE : 2*Real.exp 1≤t) (hL : x^12=Real.log t)
    (hvlo : t/2≤v) (hvhi : v≤3*t) :
    4≤v ∧ 1≤Real.log v ∧ Real.log v≤2*x^12 := by
  have htp : 0<t := by linarith
  have hvp : 0<v := by linarith
  have hloglo : 1≤Real.log v :=
    (Real.le_log_iff_exp_le hvp).mpr (by linarith)
  have hvtt : v≤t*t := by nlinarith
  have hloghi := Real.log_le_log hvp hvtt
  rw [Real.log_mul htp.ne' htp.ne'] at hloghi
  exact ⟨by linarith,hloglo,by rw [hL]; linarith⟩

theorem radius_fits_growth_strip (x v : ℝ) (hx : 0<x)
    (hlog : 0<Real.log v) (hhi : Real.log v≤2*x^12) :
    radius x≤1/(Real.log v)^(2/3:ℝ) := by
  have h2 : (2:ℝ)^(2/3:ℝ)≤2 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hb : (Real.log v)^(2/3:ℝ)≤8*x^8 := by
    calc
      _ ≤ (2*x^12)^(2/3:ℝ) := Real.rpow_le_rpow hlog.le hhi (by norm_num)
      _ = (2:ℝ)^(2/3:ℝ)*x^8 := by
        rw [Real.mul_rpow (by norm_num) (pow_nonneg hx.le 12),pow_twelve_rpow x hx]
      _ ≤ 8*x^8 := by nlinarith [pow_nonneg hx.le 8]
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlog _) hb

/-- The complete original closed disk lies in the modulus strip. Boundary
zeros are allowed. tau ranges continuously over [t,2t], not just two samples. -/
theorem translated_disk_geometry (x t tau zRe zIm : ℝ)
    (hx : 64≤x) (ht : 9≤t) (htE : 2*Real.exp 1≤t)
    (hL : x^12=Real.log t) (htau : t≤tau) (htau2 : tau≤2*t)
    (hRe : |zRe|≤radius x) (hIm : |zIm|≤radius x) :
    t/2≤tau+zIm ∧ tau+zIm≤3*t ∧
    1-1/(Real.log (tau+zIm))^(2/3:ℝ)≤1+step x+zRe ∧
    1+step x+zRe≤2 := by
  obtain ⟨hh,hh1,hR,hR1,_⟩ := scale_guards 0 x hx
  have hr := abs_le.mp hRe
  have hi := abs_le.mp hIm
  have hlo : t/2≤tau+zIm := by linarith
  have hhi : tau+zIm≤3*t := by linarith
  have hb := nearby_log_bounds t x (tau+zIm) ht htE hL hlo hhi
  have hfit := radius_fits_growth_strip x (tau+zIm) (by linarith)
    (by linarith [hb.2.1]) hb.2.2
  exact ⟨hlo,hhi,by linarith,by linarith⟩

theorem relative_power_budget (A : ℕ) (c C x : ℝ)
    (hc : 0<c) (hC : 0≤C) (hx : 0<x)
    (hcap : (2:ℝ)^(A+1)*C≤c*x^3) :
    C*(2*x^12)^A≤Real.exp (growth A x)*(c/(2*x^21)) := by
  have hid : Real.exp (growth A x)*(c/(2*x^21))=
      (c*x^3/2)*x^(12*A) := by
    rw [exp_growth A x hx,
      show 12*(A+2)=12*A+24 by omega,pow_add]
    field_simp [hx.ne']
    <;> ring
  have hlhs : C*(2*x^12)^A=C*(2:ℝ)^A*x^(12*A) := by
    rw [mul_pow,←pow_mul]
    ring
  rw [hid,hlhs]
  have hbase : C*(2:ℝ)^A≤c*x^3/2 := by
    rw [pow_succ] at hcap
    nlinarith
  exact mul_le_mul_of_nonneg_right hbase (pow_nonneg hx.le (12*A))

/-- Actual original-circle growth. Anchor and scalar budget are intermediate
quantities; the eventual zeta theorem below supplies them internally. -/
theorem disk_growth_of_modulus (A : ℕ) (c C Tg x t tau : ℝ)
    (hc : 0<c) (hC : 0≤C) (hg : LogarithmicZetaGrowth A C Tg)
    (hx : 64≤x) (ht : 9≤t) (htE : 2*Real.exp 1≤t) (htg : 2*Tg≤t)
    (hL : x^12=Real.log t) (htau : t≤tau) (htau2 : tau≤2*t)
    (hcap : (2:ℝ)^(A+1)*C≤c*x^3)
    (ha : ∀ h v : ℝ, 0<h → h≤1 → 4≤v → 1≤Real.log v →
      c*h/Real.log v≤‖riemannZeta (((1+h:ℝ):ℂ)+(v:ℂ)*Complex.I)‖) :
    DiskGrowth (1+step x) tau (radius x) (growth A x) := by
  have hxp : 0<x := by linarith
  have hcenter := nearby_log_bounds t x tau ht htE hL (by linarith) (by linarith)
  have han := scaled_center_anchor c x tau hc (by linarith)
    hcenter.1 hcenter.2.1 hcenter.2.2 ha
  intro z hz
  have hn : ‖z‖=radius x := by simpa [Metric.mem_sphere,dist_eq_norm] using hz
  have hre : |z.re|≤radius x := by simpa [hn] using Complex.abs_re_le_norm z
  have him : |z.im|≤radius x := by simpa [hn] using Complex.abs_im_le_norm z
  obtain ⟨hlo,hhi,hslo,hshi⟩ := translated_disk_geometry x t tau z.re z.im
    hx ht htE hL htau htau2 hre him
  have hlogs := nearby_log_bounds t x (tau+z.im) ht htE hL hlo hhi
  have hm := hg (1+step x+z.re) (tau+z.im) (by linarith) hslo hshi
  have he : ((1+step x+z.re:ℝ):ℂ)+((tau+z.im:ℝ):ℂ)*Complex.I=
      center (1+step x) tau+z := by
    apply Complex.ext <;> simp [Item1AutomaticZetaDetector.center] <;> ring
  rw [he] at hm
  have hu : ‖shifted (1+step x) tau z‖≤C*(2*x^12)^A := by
    apply hm.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0≤Real.log (tau+z.im)) hlogs.2.2 A) hC
  have hb := relative_power_budget A c C x hc hC hxp hcap
  have han' : c/(2*x^21)≤‖shifted (1+step x) tau 0‖ := by
    simpa [shifted,Item1AutomaticZetaDetector.center] using han
  exact (hu.trans hb).trans (mul_le_mul_of_nonneg_left han' (Real.exp_pos _).le)

#print axioms disk_growth_of_modulus
run_cmd do
  for target in [``nearby_log_bounds, ``radius_fits_growth_strip,
    ``translated_disk_geometry, ``relative_power_budget, ``disk_growth_of_modulus] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Item1ShrinkingCircleGrowth
