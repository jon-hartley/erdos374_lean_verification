import UpperProfileGridPrefix

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace UpperProfileGridArithmetic

def scale : ℕ := 1000000000000
def ceilDiv (n d : ℕ) : ℕ := (n+d-1)/d
def denominator (i k : ℕ) : ℕ := (80+i)*k+400*(40+i)
def roundedInverse (i k : ℕ) : ℕ := ceilDiv (16000*scale) (denominator i k)
def forcingCount (i : ℕ) : ℕ := ceilDiv (400*(80-i)) (80+i)
def outerCount (i j : ℕ) : ℕ := ceilDiv (400*(80+j+1-i)) (80+i)
def prefixLength (i : ℕ) : ℕ := outerCount i 719

def positiveNumerator (i j : ℕ) (p : ℕ → ℕ) : ℕ :=
  (j+1)*p (forcingCount i)+(j+121)*(p (outerCount i j)-p (forcingCount i))
def matrixEntry (i : ℕ) (p : ℕ → ℕ) (j : ℕ) : ℕ :=
  ceilDiv (positiveNumerator i j p) 16000-
    (outerCount i j-forcingCount i)*(scale/400)
def forceEntry (i : ℕ) (p : ℕ → ℕ) : ℕ :=
  ceilDiv (3*p (forcingCount i)) 400-forcingCount i*(scale/400)

theorem ceilDiv_bound (n d : ℕ) (hd : 0 < d) : n ≤ ceilDiv n d*d := by
  have h := Nat.mod_lt (n+d-1) hd
  have he := Nat.mod_add_div (n+d-1) d
  rw [Nat.mul_comm d] at he
  unfold ceilDiv
  omega

theorem lt_ceilDiv_iff (n d k : ℕ) (hd : 0 < d) :
    k < ceilDiv n d ↔ k*d < n := by
  rw [ceilDiv, Nat.lt_div_iff_mul_lt hd]
  omega

theorem denominator_pos (i k : ℕ) : 0 < denominator i k := by
  unfold denominator
  omega

theorem forcing_split (i k : ℕ) :
    denominator i k < 48000 ↔ k < forcingCount i := by
  rw [forcingCount, lt_ceilDiv_iff _ _ _ (by omega)]
  rw [Nat.mul_comm k]
  unfold denominator
  omega

theorem outer_active (i j k : ℕ) (hk : k < outerCount i j) :
    denominator i k < 400*(121+j) := by
  rw [outerCount, lt_ceilDiv_iff _ _ _ (by omega)] at hk
  rw [Nat.mul_comm k] at hk
  unfold denominator
  omega

theorem forcing_le_outer (i j : ℕ) : forcingCount i ≤ outerCount i j := by
  unfold forcingCount outerCount ceilDiv
  apply Nat.div_le_div_right
  omega

theorem outer_mono (i j l : ℕ) (hjl : j ≤ l) : outerCount i j ≤ outerCount i l := by
  unfold outerCount ceilDiv
  apply Nat.div_le_div_right
  omega

theorem outer_le_prefixLength (i j : ℕ) (hj : j < 720) :
    outerCount i j ≤ prefixLength i := outer_mono i j 719 (by omega)

theorem outer_cover (i j : ℕ) :
    400*(121+j+40) ≤ (80+i)*(400+outerCount i j) := by
  have h := ceilDiv_bound (400*(80+j+1-i)) (80+i) (by omega)
  change 400*(80+j+1-i) ≤ outerCount i j*(80+i) at h
  rw [Nat.mul_comm (outerCount i j)] at h
  have he : (80+i)*(400+outerCount i j) = 400*(80+i)+(80+i)*outerCount i j := by ring
  rw [he]
  omega

theorem forcing_cover (i : ℕ) : 64000 ≤ (80+i)*(400+forcingCount i) := by
  have h := ceilDiv_bound (400*(80-i)) (80+i) (by omega)
  change 400*(80-i) ≤ forcingCount i*(80+i) at h
  rw [Nat.mul_comm (forcingCount i)] at h
  have he : (80+i)*(400+forcingCount i) = 400*(80+i)+(80+i)*forcingCount i := by ring
  rw [he]
  omega

theorem ceilDiv_real_bound (n d : ℕ) (hd : 0 < d) :
    (n : ℝ)/(d : ℝ) ≤ (ceilDiv n d : ℝ) := by
  apply (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ)<d)).mpr
  exact_mod_cast ceilDiv_bound n d hd

theorem cast_sub_bound (n m : ℕ) : (n : ℝ)-(m : ℝ) ≤ ((n-m : ℕ) : ℝ) := by
  by_cases h : m ≤ n
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]
    have h' : (n : ℝ) ≤ m := by exact_mod_cast (show n ≤ m by omega)
    linarith

run_cmd do
  for decl in [``ceilDiv_bound, ``lt_ceilDiv_iff, ``denominator_pos, ``forcing_split,
      ``outer_active, ``forcing_le_outer, ``outer_mono, ``outer_le_prefixLength,
      ``outer_cover, ``forcing_cover, ``ceilDiv_real_bound, ``cast_sub_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "FINITE UPPER PROFILE GRID INTEGER GEOMETRY"
end UpperProfileGridArithmetic
