import PrimeNumberTheoremAnd.ZetaBounds
import Item1ZetaDiskGeometry

/-!
Original-source integration. The exact imported module name and
Zeta0EqZeta, riemannZeta0, ZetaBnd_aux1b, ZetaLowerBound3 signatures were read
from the retained Update152 component. Their historical proof tree is not
recompiled here. No stronger zero-free region is used in this file.
-/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
open Set Metric Complex MeasureTheory
namespace Item1ZetaElementaryDisk
open Item1ZetaDiskGeometry

def eulerRemainder (σ y : ℝ) : ℂ :=
  ∫ x in Ioi (1:ℝ), (((Int.floor x:ℤ):ℂ)+1/2-(x:ℂ)) /
    (x:ℂ)^(((σ:ℂ)+(y:ℂ)*Complex.I)+1)

/-- N=1 in the ACTUAL retained Euler--Maclaurin continuation. -/
theorem euler_one (σ y : ℝ) (hσ : 0<σ) (hy : 0<y) :
    riemannZeta ((σ:ℂ)+(y:ℂ)*Complex.I) =
      (1/2:ℂ)+1/(((σ:ℂ)+(y:ℂ)*Complex.I)-1)+
      ((σ:ℂ)+(y:ℂ)*Complex.I)*eulerRemainder σ y := by
  let s : ℂ := (σ:ℂ)+(y:ℂ)*Complex.I
  have hs0 : s≠0 := by
    intro he; have hi := congrArg Complex.im he
    simp [s] at hi; linarith
  have hs1 : s≠1 := by
    intro he; have hi := congrArg Complex.im he
    simp [s] at hi; linarith
  have hz := Zeta0EqZeta (N:=1) (by norm_num)
    (s:=s) (by simpa [s] using hσ) hs1
  rw [←hz]
  simp only [riemannZeta0,Finset.sum_range_succ,Finset.sum_range_zero,
    zero_add,Nat.cast_zero,Nat.cast_one,Complex.one_cpow,
    Complex.zero_cpow hs0,div_zero,one_div_one]
  dsimp [s,eulerRemainder]
  have he : (1:ℂ)-((σ:ℂ)+(y:ℂ)*Complex.I) =
      -(((σ:ℂ)+(y:ℂ)*Complex.I)-1) := by ring
  rw [he,div_neg]
  ring

theorem remainder_norm (σ y : ℝ) (hσ : 0<σ) :
    ‖eulerRemainder σ y‖≤1/σ := by
  have h := ZetaBnd_aux1b 1 (by norm_num) (σ:=σ) (t:=y) hσ
  simpa only [eulerRemainder,Nat.cast_one,Real.one_rpow] using h

/-- Coarse polynomial growth, much weaker than any subcritical zero-free
input: sigma in [1/2,4], positive height at least 4. -/
theorem coarse_zeta_growth (σ y : ℝ) (hσ : 1/2≤σ) (hσ1 : σ≤4)
    (hy : 4≤y) :
    ‖riemannZeta ((σ:ℂ)+(y:ℂ)*Complex.I)‖≤6*y := by
  let s : ℂ := (σ:ℂ)+(y:ℂ)*Complex.I
  have hσp : 0<σ := by linarith
  have hyp : 0<y := by linarith
  have hsn : ‖s‖≤4+y := by
    have h := norm_add_le (σ:ℂ) ((y:ℂ)*Complex.I)
    have hh : ‖s‖≤σ+y := by
      simpa [s,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hσp.le,
        abs_of_nonneg hyp.le] using h
    linarith
  have hin : y≤‖s-1‖ := by
    simpa [s,abs_of_nonneg hyp.le] using abs_im_le_norm (s-1)
  have hi : ‖(1:ℂ)/(s-1)‖≤1 := by
    rw [norm_div,norm_one]
    apply (div_le_one (by linarith : 0<‖s-1‖)).mpr
    linarith
  have hr : ‖eulerRemainder σ y‖≤2 := by
    apply (remainder_norm σ y hσp).trans
    apply (div_le_iff₀ hσp).mpr
    linarith
  rw [euler_one σ y hσp hyp]
  calc
    _ ≤ ‖(1/2:ℂ)‖+‖(1:ℂ)/(s-1)‖+‖s*eulerRemainder σ y‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 1/2+1+(4+y)*2 := by
      rw [show ‖(1/2:ℂ)‖=(1/2:ℝ) by norm_num, norm_mul]
      exact add_le_add (add_le_add le_rfl hi)
        (mul_le_mul hsn hr (norm_nonneg _) (by linarith))
    _ ≤ 6*y := by linarith

/-- The retained right-of-one lower bound supplies a deliberately weak
anchor c/y. This is not a new nonvanishing assumption. -/
theorem exists_coarse_anchor :
    ∃ c : ℝ, 0<c ∧ ∀ y : ℝ, 4≤y → 1≤Real.log y →
      c/y≤‖riemannZeta (center y)‖ := by
  obtain ⟨c,hc,hbound⟩ := ZetaLowerBound3
  refine ⟨c,hc,?_⟩
  intro y hy hlog
  have hyp : 0<y := by linarith
  have hLp : 0<Real.log y := by linarith
  have h := hbound (σ:=2) (by norm_num) y
    (by rw [abs_of_pos hyp]; linarith)
  have hr : (Real.log y)^(1/4:ℝ)≤y := by
    apply (Real.rpow_le_self_of_one_le hlog (by norm_num)).trans
    linarith [Real.log_le_sub_one_of_pos hyp]
  have hp : 0<(Real.log y)^(1/4:ℝ) := Real.rpow_pos_of_pos hLp _
  apply (div_le_div_of_nonneg_left hc.le hp hr).trans
  norm_num [Item1ZetaDiskGeometry.center, abs_of_pos hyp] at h ⊢
  exact h

/-- An upper modulus bound relative to the fixed center, with M=3 log y.
Its anchor and modulus data are supplied from the preceding source calls. -/
theorem relative_disk_growth (c b y : ℝ) (hc : 0<c)
    (hy : 8≤y) (hlog : 1≤Real.log y) (hyc : 16/c≤y)
    (hd : depth b y≤1/4)
    (hanchor : c/y≤‖riemannZeta (center y)‖) :
    ∀ w∈ball (center y) (1+2*depth b y),
      ‖riemannZeta w‖≤Real.exp (3*Real.log y)*‖riemannZeta (center y)‖ := by
  intro w hw
  obtain ⟨hrlo,hrhi,hylo,hyhi⟩ := disk_coordinates y (depth b y) (by linarith) hd w hw
  have hsmall : ‖riemannZeta w‖≤16*y := by
    have h := coarse_zeta_growth w.re w.im (by linarith) hrhi.le (by linarith)
    simp only [Complex.re_add_im] at h
    linarith
  have hyp : 0<y := by linarith
  have he : Real.exp (3*Real.log y)=y*y*y := by
    rw [show 3*Real.log y=Real.log y+Real.log y+Real.log y by ring,
      Real.exp_add,Real.exp_add,Real.exp_log hyp]
  have hcy : 16≤c*y := by
    have h := (div_le_iff₀ hc).mp hyc
    nlinarith
  calc
    ‖riemannZeta w‖ ≤ 16*y := hsmall
    _ ≤ (y*y*y)*(c/y) := by
      field_simp
      nlinarith [mul_le_mul_of_nonneg_right hcy (sq_nonneg y)]
    _ ≤ (y*y*y)*‖riemannZeta (center y)‖ :=
      mul_le_mul_of_nonneg_left hanchor (by positivity)
    _ = Real.exp (3*Real.log y)*‖riemannZeta (center y)‖ := by rw [he]

#print axioms euler_one
#print axioms remainder_norm
#print axioms coarse_zeta_growth
#print axioms exists_coarse_anchor
#print axioms relative_disk_growth

run_cmd do
  for target in [``euler_one, ``remainder_norm, ``coarse_zeta_growth,
    ``exists_coarse_anchor, ``relative_disk_growth] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"

end Item1ZetaElementaryDisk
