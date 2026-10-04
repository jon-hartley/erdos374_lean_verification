import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-! The only arithmetic proposition introduced here is literal
nonvanishing of riemannZeta. It is NOT proved in this package. The disk
inclusions below are elementary and retain a strict boundary margin. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open Set Metric Complex
namespace Item1ZetaDiskGeometry

def BarePositiveZeroFree (b T₀ : ℝ) : Prop :=
  ∀ σ y : ℝ, T₀ ≤ y →
    1-b/(Real.log y)^(3/4:ℝ) ≤ σ → σ ≤ 4 →
    riemannZeta ((σ:ℂ)+(y:ℂ)*Complex.I) ≠ 0

def center (y : ℝ) : ℂ := 2+(y:ℂ)*Complex.I
def depth (b y : ℝ) : ℝ := b/(8*(Real.log y)^(3/4:ℝ))

theorem depth_guards (b y : ℝ) (hb : 0<b) (hb1 : b≤1/2)
    (hlog : 1≤Real.log y) : 0<depth b y ∧ depth b y≤1/4 := by
  have hp : 0<(Real.log y)^(3/4:ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have h1 : 1≤(Real.log y)^(3/4:ℝ) := by
    simpa using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1) hlog
      (by norm_num : (0:ℝ)≤3/4)
  constructor
  · exact div_pos hb (by positivity)
  · unfold depth
    apply (div_le_iff₀ (by positivity : 0<8*(Real.log y)^(3/4:ℝ))).mpr
    linarith

theorem disk_coordinates (y d : ℝ) (hy : 4≤y) (hd : d≤1/4)
    (w : ℂ) (hw : w∈ball (center y) (1+2*d)) :
    1-2*d<w.re ∧ w.re<4 ∧ y/2<w.im ∧ w.im<2*y := by
  have hn : ‖w-center y‖<1+2*d := by simpa [mem_ball,dist_eq_norm] using hw
  have hre := (abs_re_le_norm (w-center y)).trans_lt hn
  have him := (abs_im_le_norm (w-center y)).trans_lt hn
  norm_num [center] at hre him
  have hr := abs_lt.mp hre
  have hi := abs_lt.mp him
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem target_inner (b y σ : ℝ) (hσ : 1-depth b y≤σ) (hσ1 : σ≤2) :
    ‖((σ:ℂ)+(y:ℂ)*Complex.I)-center y‖≤1+depth b y := by
  have he : ((σ:ℂ)+(y:ℂ)*Complex.I)-center y = ((σ-2:ℝ):ℂ) := by
    unfold center; push_cast; ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
  linarith

/-- The outer disk fits in the hypothesized zero-free region, not just the
smaller target strip. Nearby heights are explicitly compared. -/
theorem disk_nonvanishing (b T₀ y : ℝ) (hb : 0<b) (hb1 : b≤1/2)
    (hT : 4≤T₀) (hy : 4≤y) (hyT : 2*T₀≤y) (hlog : 1≤Real.log y)
    (hzero : BarePositiveZeroFree b T₀) :
    ∀ w∈ball (center y) (1+2*depth b y), riemannZeta w≠0 := by
  intro w hw
  obtain ⟨hd,hd1⟩ := depth_guards b y hb hb1 hlog
  obtain ⟨hrlo,hrhi,hylo,hyhi⟩ := disk_coordinates y (depth b y) hy hd1 w hw
  have hwT : T₀≤w.im := by linarith
  have hwp : 0<w.im := by linarith
  have hL : 0<Real.log y := by linarith
  have hLw : 0<Real.log w.im := Real.log_pos (by linarith)
  have hlogs : Real.log w.im≤2*Real.log y := by
    calc
      Real.log w.im ≤ Real.log (2*y) := Real.log_le_log hwp hyhi.le
      _ = Real.log 2+Real.log y := Real.log_mul (by norm_num) (by linarith)
      _ ≤ 2*Real.log y := by
        have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : (2:ℝ)≤y)
        linarith
  have hP : 0<(Real.log y)^(3/4:ℝ) := Real.rpow_pos_of_pos hL _
  have hPw : 0<(Real.log w.im)^(3/4:ℝ) := Real.rpow_pos_of_pos hLw _
  have hpower : (Real.log w.im)^(3/4:ℝ)≤2*(Real.log y)^(3/4:ℝ) := by
    calc
      _ ≤ (2*Real.log y)^(3/4:ℝ) :=
        Real.rpow_le_rpow hLw.le hlogs (by norm_num)
      _ = (2:ℝ)^(3/4:ℝ)*(Real.log y)^(3/4:ℝ) :=
        Real.mul_rpow (by norm_num) hL.le
      _ ≤ 2*(Real.log y)^(3/4:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hP.le
        exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hmargin : 2*depth b y ≤ b/(Real.log w.im)^(3/4:ℝ) := by
    apply (le_div_iff₀ hPw).mpr
    calc
      (2*depth b y)*(Real.log w.im)^(3/4:ℝ)
          ≤ (2*depth b y)*(2*(Real.log y)^(3/4:ℝ)) :=
            mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = b/2 := by unfold depth; field_simp; ring
      _ ≤ b := by linarith
  have hz := hzero w.re w.im hwT (by linarith) hrhi.le
  simpa only [Complex.re_add_im] using hz

theorem zeta_differentiable_disk (y d : ℝ) (hy : 4≤y) (hd : d≤1/4) :
    DifferentiableOn ℂ riemannZeta (ball (center y) (1+2*d)) := by
  intro w hw
  have hi := (disk_coordinates y d hy hd w hw).2.2.1
  apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
  intro he
  have him := congrArg Complex.im he
  norm_num at him
  linarith

/-- The deliberately loose disk derivative loss is still far below log^9. -/
theorem depth_budget (b y : ℝ) (hb : 0<b) (hL : 1≤Real.log y) :
    16*(3*Real.log y)/(depth b y)^2 ≤ (3072/b^2)*(Real.log y)^9 := by
  have hLp : 0<Real.log y := by linarith
  have hp : 0<(Real.log y)^(3/4:ℝ) := Real.rpow_pos_of_pos hLp _
  have he : ((Real.log y)^(3/4:ℝ))^2 = (Real.log y)^(3/2:ℝ) := by
    rw [←Real.rpow_mul_natCast hLp.le (3/4:ℝ) 2]
    norm_num
  have he' : Real.log y*(Real.log y)^(3/2:ℝ) = (Real.log y)^(5/2:ℝ) := by
    calc
      _ = (Real.log y)^(1:ℝ)*(Real.log y)^(3/2:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hLp]; norm_num
  have hid : 16*(3*Real.log y)/(depth b y)^2 =
      (3072/b^2)*(Real.log y)^(5/2:ℝ) := by
    unfold depth
    field_simp
    rw [he]
    nlinarith [he']
  rw [hid]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  convert
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (5/2:ℝ)≤(9:ℝ))
    using 1 <;> norm_num

end Item1ZetaDiskGeometry

run_cmd do
  for target in [``Item1ZetaDiskGeometry.depth_guards,
    ``Item1ZetaDiskGeometry.disk_coordinates,
    ``Item1ZetaDiskGeometry.target_inner,
    ``Item1ZetaDiskGeometry.disk_nonvanishing,
    ``Item1ZetaDiskGeometry.zeta_differentiable_disk,
    ``Item1ZetaDiskGeometry.depth_budget] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1ZetaDiskGeometry.disk_nonvanishing
#print axioms Item1ZetaDiskGeometry.depth_budget
