import SingletonHarmonicMoving

/-! A reusable width-freezing adapter for a fixed-width estimate linear in
the width and interval length. Its explicit hypothesis is discharged by the
Fourier estimate in the application module. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory

namespace PairMovingKernel
open SingletonMoving SingletonHarmonic SingletonHarmonicMoving SingletonHarmonicPartition

def FixedBound (Q : ℕ) (B u v w r : ℝ) : Prop :=
  ∀ (a : ℕ → ℝ), (∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) →
    ∀ h t T : ℝ, 0 ≤ h → 0 ≤ T →
      (∫ x in t..t+T, remainder (Finset.Icc 1 Q) a x h ^ 2) ≤
        B^2 * (T * (h*u+w) + h*v+r)

theorem block_bound (Q : ℕ) (a : ℕ → ℝ) (B u v w r : ℝ)
    (hf : FixedBound Q B u v w r) (h : ℝ → ℝ) (hh : Measurable h)
    (k E t T : ℝ) (hk0 : 0 ≤ k) (hT : 0 ≤ T) (hE0 : 0 ≤ E)
    (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B)
    (hk : ∀ x ∈ Set.Icc t (t+T), k ≤ h x)
    (hE : ∀ x ∈ Set.Icc t (t+T), h x-k ≤ E) :
    (∫ x in t..t+T, remainder (Finset.Icc 1 Q) a x (h x)^2) ≤
      B^2 * (T*(3*(k+E)*u+6*w+12*E^2*harmonicSum Q^2) +
        3*(k+E)*v+6*r) := by
  have hfrozen := hf a ha k t T hk0 hT
  have haux := hf (fun n => |a n|) (by simpa only [abs_abs] using ha) E (t-k) T hE0 hT
  have hshift : (∫ x in t..t+T,
      remainder (Finset.Icc 1 Q) (fun n => |a n|) (x-k) E^2) =
      (∫ x in t-k..(t-k)+T, remainder (Finset.Icc 1 Q) (fun n => |a n|) x E^2) := by
    have ht := intervalIntegral.integral_comp_sub_right
      (f := fun x => remainder (Finset.Icc 1 Q) (fun n => |a n|) x E^2)
      (a := t) (b := t+T) k
    simpa only [show t+T-k=(t-k)+T by ring] using ht
  rw [← hshift] at haux
  have hm := mass_abs_le Q a B ha
  have hm0 := mass_abs_nonneg (Finset.Icc 1 Q) a
  have htwo : 0 ≤ 2*E := by positivity
  have hm2 := pow_le_pow_left₀ (mul_nonneg htwo hm0)
    (mul_le_mul_of_nonneg_left hm htwo) 2
  calc
    _ ≤ 3*((∫ x in t..t+T, remainder (Finset.Icc 1 Q) a x k^2) +
        (∫ x in t..t+T, remainder (Finset.Icc 1 Q) (fun n => |a n|) (x-k) E^2) +
        T*(2*E*mass (Finset.Icc 1 Q) (fun n => |a n|))^2) :=
      integral_square_freeze_le (Finset.Icc 1 Q) a h hh k E t T hT hE0 hk hE
    _ ≤ 3*(B^2*(T*(k*u+w)+k*v+r) + B^2*(T*(E*u+w)+E*v+r) +
        T*(2*E*(B*harmonicSum Q))^2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hfrozen haux) (mul_le_mul_of_nonneg_left hm2 hT))
        (by norm_num)
    _ = _ := by ring

theorem moving_bound (Q : ℕ) (a : ℕ → ℝ) (B u v w r X H : ℝ)
    (hf : FixedBound Q B u v w r) (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ r)
    (hX : 0 < X) (hH : 1 ≤ H) (ha : ∀ n ∈ Finset.Icc 1 Q, |a n| ≤ B) :
    (1/X)*(∫ x in X..2*X, remainder (Finset.Icc 1 Q) a x (x*H/X)^2) ≤
      B^2*((6*H+3)*u+6*w+12*harmonicSum Q^2+
        (2*H/X)*((6*H+3)*v+6*r)) := by
  have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH
  let L : ℝ := X/H
  have hL : 0 < L := div_pos hX hH0
  have hLX : L ≤ X := by
    dsimp [L]
    apply (div_le_iff₀ hH0).mpr
    nlinarith
  have hLH : L*H/X=1 := by dsimp [L]; field_simp
  have hmeas : Measurable (fun x : ℝ => x*H/X) := by fun_prop
  have hi := square_intervalIntegrable_comp (Finset.Icc 1 Q) a id
    (fun x : ℝ => x*H/X) measurable_id hmeas X (X+X)
  simp only [id_eq] at hi
  let A : ℝ := B^2*((6*H+3)*u+6*w+12*harmonicSum Q^2)
  let C : ℝ := B^2*((6*H+3)*v+6*r)
  have hblocks : ∀ j < blockCount X L,
      (∫ x in point X X L j..point X X L (j+1),
        remainder (Finset.Icc 1 Q) a x (x*H/X)^2) ≤
        A*(point X X L (j+1)-point X X L j)+C := by
    intro j _
    let t : ℝ := point X X L j
    let T : ℝ := point X X L (j+1)-point X X L j
    let k : ℝ := t*H/X
    have ht : X ≤ t := point_lower X X L hX.le hL.le j
    have ht2 : t ≤ 2*X := by
      have h := point_upper X X L j
      dsimp [t]
      linarith
    have hT : 0 ≤ T := block_length_nonneg X X L hL.le j
    have hTL : T ≤ L := block_length_le X X L hL.le j
    have hk0 : 0 ≤ k := div_nonneg (mul_nonneg (hX.le.trans ht) hH0.le) hX.le
    have hk2 : k ≤ 2*H := by
      apply (div_le_iff₀ hX).mpr
      nlinarith
    have hkk : ∀ x ∈ Set.Icc t (t+T), k ≤ x*H/X := by
      intro x hx
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hx.1 hH0.le) hX.le
    have hke : ∀ x ∈ Set.Icc t (t+T), x*H/X-k ≤ 1 := by
      intro x hx
      have hxt : x-t ≤ L := by linarith [hx.2]
      have hm := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hxt hH0.le) hX.le
      rw [hLH] at hm
      dsimp [k]
      calc
        x*H/X-t*H/X=(x-t)*H/X := by ring
        _ ≤ 1 := hm
    have hb := block_bound Q a B u v w r hf (fun x => x*H/X) hmeas
      k 1 t T hk0 hT (by norm_num) ha hkk hke
    have hend : t+T=point X X L (j+1) := by dsimp [t,T]; ring
    rw [hend] at hb
    have hcu : 3*(k+1)*u ≤ (6*H+3)*u := by nlinarith
    have hcv : 3*(k+1)*v ≤ (6*H+3)*v := by nlinarith
    apply hb.trans
    change _ ≤ A*T+C
    dsimp only [A,C]
    have he : B^2*(T*((6*H+3)*u+6*w+12*harmonicSum Q^2)+
        (6*H+3)*v+6*r) =
        B^2*((6*H+3)*u+6*w+12*harmonicSum Q^2)*T+B^2*((6*H+3)*v+6*r) := by ring
    rw [← he]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
    norm_num only [one_pow, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left hcu hT]
  have hwhole := integral_le_of_blocks
    (fun x => remainder (Finset.Icc 1 Q) a x (x*H/X)^2)
    X X L A C hX.le hL hi hblocks
  have hJ : (blockCount X L : ℝ) ≤ 2*H := by
    have h := blockCount_le_two_ratio X L hL hLX
    have he : X/L=H := by dsimp [L]; field_simp
    simpa only [he] using h
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hwhole' : (∫ x in X..2*X, remainder (Finset.Icc 1 Q) a x (x*H/X)^2) ≤
      A*X+2*H*C := by
    rw [show 2*X=X+X by ring]
    exact hwhole.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hJ hC))
  have hnorm := mul_le_mul_of_nonneg_left hwhole' (le_of_lt (one_div_pos.mpr hX))
  convert hnorm using 1
  dsimp [A,C]
  field_simp

end PairMovingKernel
