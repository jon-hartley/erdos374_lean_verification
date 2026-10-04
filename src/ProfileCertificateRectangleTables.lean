import ProfileCertificateTables
import ProfileCertificateRectangles

set_option autoImplicit false
set_option maxHeartbeats 20000000

set_option maxRecDepth 10000
namespace ProfileCertificateRectangleTables

open ProfileCertificateArithmetic ProfileCertificateTables ProfileCertificateRectangles

run_cmd Lean.logInfo "LITERAL RECTANGLES: submitting row block 0 through 9"

theorem row0_literal : ∀ j : Fin 90,
    (row0[j.val]! : ℤ) = roundedCumulative 0 j.val ∧
    (outerCount 0 j.val = 0 ∨ denominator 0 (outerCount 0 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (0+10)*(50+outerCount 0 j.val) := by decide

theorem row1_literal : ∀ j : Fin 90,
    (row1[j.val]! : ℤ) = roundedCumulative 1 j.val ∧
    (outerCount 1 j.val = 0 ∨ denominator 1 (outerCount 1 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (1+10)*(50+outerCount 1 j.val) := by decide

theorem row2_literal : ∀ j : Fin 90,
    (row2[j.val]! : ℤ) = roundedCumulative 2 j.val ∧
    (outerCount 2 j.val = 0 ∨ denominator 2 (outerCount 2 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (2+10)*(50+outerCount 2 j.val) := by decide

theorem row3_literal : ∀ j : Fin 90,
    (row3[j.val]! : ℤ) = roundedCumulative 3 j.val ∧
    (outerCount 3 j.val = 0 ∨ denominator 3 (outerCount 3 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (3+10)*(50+outerCount 3 j.val) := by decide

theorem row4_literal : ∀ j : Fin 90,
    (row4[j.val]! : ℤ) = roundedCumulative 4 j.val ∧
    (outerCount 4 j.val = 0 ∨ denominator 4 (outerCount 4 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (4+10)*(50+outerCount 4 j.val) := by decide

theorem row5_literal : ∀ j : Fin 90,
    (row5[j.val]! : ℤ) = roundedCumulative 5 j.val ∧
    (outerCount 5 j.val = 0 ∨ denominator 5 (outerCount 5 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (5+10)*(50+outerCount 5 j.val) := by decide

theorem row6_literal : ∀ j : Fin 90,
    (row6[j.val]! : ℤ) = roundedCumulative 6 j.val ∧
    (outerCount 6 j.val = 0 ∨ denominator 6 (outerCount 6 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (6+10)*(50+outerCount 6 j.val) := by decide

theorem row7_literal : ∀ j : Fin 90,
    (row7[j.val]! : ℤ) = roundedCumulative 7 j.val ∧
    (outerCount 7 j.val = 0 ∨ denominator 7 (outerCount 7 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (7+10)*(50+outerCount 7 j.val) := by decide

theorem row8_literal : ∀ j : Fin 90,
    (row8[j.val]! : ℤ) = roundedCumulative 8 j.val ∧
    (outerCount 8 j.val = 0 ∨ denominator 8 (outerCount 8 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (8+10)*(50+outerCount 8 j.val) := by decide

theorem row9_literal : ∀ j : Fin 90,
    (row9[j.val]! : ℤ) = roundedCumulative 9 j.val ∧
    (outerCount 9 j.val = 0 ∨ denominator 9 (outerCount 9 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (9+10)*(50+outerCount 9 j.val) := by decide

run_cmd Lean.logInfo "LITERAL RECTANGLES: submitting row block 10 through 19"

theorem row10_literal : ∀ j : Fin 90,
    (row10[j.val]! : ℤ) = roundedCumulative 10 j.val ∧
    (outerCount 10 j.val = 0 ∨ denominator 10 (outerCount 10 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (10+10)*(50+outerCount 10 j.val) := by decide

theorem row11_literal : ∀ j : Fin 90,
    (row11[j.val]! : ℤ) = roundedCumulative 11 j.val ∧
    (outerCount 11 j.val = 0 ∨ denominator 11 (outerCount 11 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (11+10)*(50+outerCount 11 j.val) := by decide

theorem row12_literal : ∀ j : Fin 90,
    (row12[j.val]! : ℤ) = roundedCumulative 12 j.val ∧
    (outerCount 12 j.val = 0 ∨ denominator 12 (outerCount 12 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (12+10)*(50+outerCount 12 j.val) := by decide

theorem row13_literal : ∀ j : Fin 90,
    (row13[j.val]! : ℤ) = roundedCumulative 13 j.val ∧
    (outerCount 13 j.val = 0 ∨ denominator 13 (outerCount 13 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (13+10)*(50+outerCount 13 j.val) := by decide

theorem row14_literal : ∀ j : Fin 90,
    (row14[j.val]! : ℤ) = roundedCumulative 14 j.val ∧
    (outerCount 14 j.val = 0 ∨ denominator 14 (outerCount 14 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (14+10)*(50+outerCount 14 j.val) := by decide

theorem row15_literal : ∀ j : Fin 90,
    (row15[j.val]! : ℤ) = roundedCumulative 15 j.val ∧
    (outerCount 15 j.val = 0 ∨ denominator 15 (outerCount 15 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (15+10)*(50+outerCount 15 j.val) := by decide

theorem row16_literal : ∀ j : Fin 90,
    (row16[j.val]! : ℤ) = roundedCumulative 16 j.val ∧
    (outerCount 16 j.val = 0 ∨ denominator 16 (outerCount 16 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (16+10)*(50+outerCount 16 j.val) := by decide

theorem row17_literal : ∀ j : Fin 90,
    (row17[j.val]! : ℤ) = roundedCumulative 17 j.val ∧
    (outerCount 17 j.val = 0 ∨ denominator 17 (outerCount 17 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (17+10)*(50+outerCount 17 j.val) := by decide

theorem row18_literal : ∀ j : Fin 90,
    (row18[j.val]! : ℤ) = roundedCumulative 18 j.val ∧
    (outerCount 18 j.val = 0 ∨ denominator 18 (outerCount 18 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (18+10)*(50+outerCount 18 j.val) := by decide

theorem row19_literal : ∀ j : Fin 90,
    (row19[j.val]! : ℤ) = roundedCumulative 19 j.val ∧
    (outerCount 19 j.val = 0 ∨ denominator 19 (outerCount 19 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (19+10)*(50+outerCount 19 j.val) := by decide

run_cmd Lean.logInfo "LITERAL RECTANGLES: submitting row block 20 through 29"

theorem row20_literal : ∀ j : Fin 90,
    (row20[j.val]! : ℤ) = roundedCumulative 20 j.val ∧
    (outerCount 20 j.val = 0 ∨ denominator 20 (outerCount 20 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (20+10)*(50+outerCount 20 j.val) := by decide

theorem row21_literal : ∀ j : Fin 90,
    (row21[j.val]! : ℤ) = roundedCumulative 21 j.val ∧
    (outerCount 21 j.val = 0 ∨ denominator 21 (outerCount 21 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (21+10)*(50+outerCount 21 j.val) := by decide

theorem row22_literal : ∀ j : Fin 90,
    (row22[j.val]! : ℤ) = roundedCumulative 22 j.val ∧
    (outerCount 22 j.val = 0 ∨ denominator 22 (outerCount 22 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (22+10)*(50+outerCount 22 j.val) := by decide

theorem row23_literal : ∀ j : Fin 90,
    (row23[j.val]! : ℤ) = roundedCumulative 23 j.val ∧
    (outerCount 23 j.val = 0 ∨ denominator 23 (outerCount 23 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (23+10)*(50+outerCount 23 j.val) := by decide

theorem row24_literal : ∀ j : Fin 90,
    (row24[j.val]! : ℤ) = roundedCumulative 24 j.val ∧
    (outerCount 24 j.val = 0 ∨ denominator 24 (outerCount 24 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (24+10)*(50+outerCount 24 j.val) := by decide

theorem row25_literal : ∀ j : Fin 90,
    (row25[j.val]! : ℤ) = roundedCumulative 25 j.val ∧
    (outerCount 25 j.val = 0 ∨ denominator 25 (outerCount 25 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (25+10)*(50+outerCount 25 j.val) := by decide

theorem row26_literal : ∀ j : Fin 90,
    (row26[j.val]! : ℤ) = roundedCumulative 26 j.val ∧
    (outerCount 26 j.val = 0 ∨ denominator 26 (outerCount 26 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (26+10)*(50+outerCount 26 j.val) := by decide

theorem row27_literal : ∀ j : Fin 90,
    (row27[j.val]! : ℤ) = roundedCumulative 27 j.val ∧
    (outerCount 27 j.val = 0 ∨ denominator 27 (outerCount 27 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (27+10)*(50+outerCount 27 j.val) := by decide

theorem row28_literal : ∀ j : Fin 90,
    (row28[j.val]! : ℤ) = roundedCumulative 28 j.val ∧
    (outerCount 28 j.val = 0 ∨ denominator 28 (outerCount 28 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (28+10)*(50+outerCount 28 j.val) := by decide

theorem row29_literal : ∀ j : Fin 90,
    (row29[j.val]! : ℤ) = roundedCumulative 29 j.val ∧
    (outerCount 29 j.val = 0 ∨ denominator 29 (outerCount 29 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (29+10)*(50+outerCount 29 j.val) := by decide

run_cmd Lean.logInfo "LITERAL RECTANGLES: submitting row block 30 through 39"

theorem row30_literal : ∀ j : Fin 90,
    (row30[j.val]! : ℤ) = roundedCumulative 30 j.val ∧
    (outerCount 30 j.val = 0 ∨ denominator 30 (outerCount 30 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (30+10)*(50+outerCount 30 j.val) := by decide

theorem row31_literal : ∀ j : Fin 90,
    (row31[j.val]! : ℤ) = roundedCumulative 31 j.val ∧
    (outerCount 31 j.val = 0 ∨ denominator 31 (outerCount 31 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (31+10)*(50+outerCount 31 j.val) := by decide

theorem row32_literal : ∀ j : Fin 90,
    (row32[j.val]! : ℤ) = roundedCumulative 32 j.val ∧
    (outerCount 32 j.val = 0 ∨ denominator 32 (outerCount 32 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (32+10)*(50+outerCount 32 j.val) := by decide

theorem row33_literal : ∀ j : Fin 90,
    (row33[j.val]! : ℤ) = roundedCumulative 33 j.val ∧
    (outerCount 33 j.val = 0 ∨ denominator 33 (outerCount 33 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (33+10)*(50+outerCount 33 j.val) := by decide

theorem row34_literal : ∀ j : Fin 90,
    (row34[j.val]! : ℤ) = roundedCumulative 34 j.val ∧
    (outerCount 34 j.val = 0 ∨ denominator 34 (outerCount 34 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (34+10)*(50+outerCount 34 j.val) := by decide

theorem row35_literal : ∀ j : Fin 90,
    (row35[j.val]! : ℤ) = roundedCumulative 35 j.val ∧
    (outerCount 35 j.val = 0 ∨ denominator 35 (outerCount 35 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (35+10)*(50+outerCount 35 j.val) := by decide

theorem row36_literal : ∀ j : Fin 90,
    (row36[j.val]! : ℤ) = roundedCumulative 36 j.val ∧
    (outerCount 36 j.val = 0 ∨ denominator 36 (outerCount 36 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (36+10)*(50+outerCount 36 j.val) := by decide

theorem row37_literal : ∀ j : Fin 90,
    (row37[j.val]! : ℤ) = roundedCumulative 37 j.val ∧
    (outerCount 37 j.val = 0 ∨ denominator 37 (outerCount 37 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (37+10)*(50+outerCount 37 j.val) := by decide

theorem row38_literal : ∀ j : Fin 90,
    (row38[j.val]! : ℤ) = roundedCumulative 38 j.val ∧
    (outerCount 38 j.val = 0 ∨ denominator 38 (outerCount 38 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (38+10)*(50+outerCount 38 j.val) := by decide

theorem row39_literal : ∀ j : Fin 90,
    (row39[j.val]! : ℤ) = roundedCumulative 39 j.val ∧
    (outerCount 39 j.val = 0 ∨ denominator 39 (outerCount 39 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (39+10)*(50+outerCount 39 j.val) := by decide

run_cmd Lean.logInfo "LITERAL RECTANGLES: submitting row block 40 through 49"

theorem row40_literal : ∀ j : Fin 90,
    (row40[j.val]! : ℤ) = roundedCumulative 40 j.val ∧
    (outerCount 40 j.val = 0 ∨ denominator 40 (outerCount 40 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (40+10)*(50+outerCount 40 j.val) := by decide

theorem row41_literal : ∀ j : Fin 90,
    (row41[j.val]! : ℤ) = roundedCumulative 41 j.val ∧
    (outerCount 41 j.val = 0 ∨ denominator 41 (outerCount 41 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (41+10)*(50+outerCount 41 j.val) := by decide

theorem row42_literal : ∀ j : Fin 90,
    (row42[j.val]! : ℤ) = roundedCumulative 42 j.val ∧
    (outerCount 42 j.val = 0 ∨ denominator 42 (outerCount 42 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (42+10)*(50+outerCount 42 j.val) := by decide

theorem row43_literal : ∀ j : Fin 90,
    (row43[j.val]! : ℤ) = roundedCumulative 43 j.val ∧
    (outerCount 43 j.val = 0 ∨ denominator 43 (outerCount 43 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (43+10)*(50+outerCount 43 j.val) := by decide

theorem row44_literal : ∀ j : Fin 90,
    (row44[j.val]! : ℤ) = roundedCumulative 44 j.val ∧
    (outerCount 44 j.val = 0 ∨ denominator 44 (outerCount 44 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (44+10)*(50+outerCount 44 j.val) := by decide

theorem row45_literal : ∀ j : Fin 90,
    (row45[j.val]! : ℤ) = roundedCumulative 45 j.val ∧
    (outerCount 45 j.val = 0 ∨ denominator 45 (outerCount 45 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (45+10)*(50+outerCount 45 j.val) := by decide

theorem row46_literal : ∀ j : Fin 90,
    (row46[j.val]! : ℤ) = roundedCumulative 46 j.val ∧
    (outerCount 46 j.val = 0 ∨ denominator 46 (outerCount 46 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (46+10)*(50+outerCount 46 j.val) := by decide

theorem row47_literal : ∀ j : Fin 90,
    (row47[j.val]! : ℤ) = roundedCumulative 47 j.val ∧
    (outerCount 47 j.val = 0 ∨ denominator 47 (outerCount 47 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (47+10)*(50+outerCount 47 j.val) := by decide

theorem row48_literal : ∀ j : Fin 90,
    (row48[j.val]! : ℤ) = roundedCumulative 48 j.val ∧
    (outerCount 48 j.val = 0 ∨ denominator 48 (outerCount 48 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (48+10)*(50+outerCount 48 j.val) := by decide

theorem row49_literal : ∀ j : Fin 90,
    (row49[j.val]! : ℤ) = roundedCumulative 49 j.val ∧
    (outerCount 49 j.val = 0 ∨ denominator 49 (outerCount 49 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (49+10)*(50+outerCount 49 j.val) := by decide

run_cmd Lean.logInfo "LITERAL RECTANGLES: submitting row block 50 through 59"

theorem row50_literal : ∀ j : Fin 90,
    (row50[j.val]! : ℤ) = roundedCumulative 50 j.val ∧
    (outerCount 50 j.val = 0 ∨ denominator 50 (outerCount 50 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (50+10)*(50+outerCount 50 j.val) := by decide

theorem row51_literal : ∀ j : Fin 90,
    (row51[j.val]! : ℤ) = roundedCumulative 51 j.val ∧
    (outerCount 51 j.val = 0 ∨ denominator 51 (outerCount 51 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (51+10)*(50+outerCount 51 j.val) := by decide

theorem row52_literal : ∀ j : Fin 90,
    (row52[j.val]! : ℤ) = roundedCumulative 52 j.val ∧
    (outerCount 52 j.val = 0 ∨ denominator 52 (outerCount 52 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (52+10)*(50+outerCount 52 j.val) := by decide

theorem row53_literal : ∀ j : Fin 90,
    (row53[j.val]! : ℤ) = roundedCumulative 53 j.val ∧
    (outerCount 53 j.val = 0 ∨ denominator 53 (outerCount 53 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (53+10)*(50+outerCount 53 j.val) := by decide

theorem row54_literal : ∀ j : Fin 90,
    (row54[j.val]! : ℤ) = roundedCumulative 54 j.val ∧
    (outerCount 54 j.val = 0 ∨ denominator 54 (outerCount 54 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (54+10)*(50+outerCount 54 j.val) := by decide

theorem row55_literal : ∀ j : Fin 90,
    (row55[j.val]! : ℤ) = roundedCumulative 55 j.val ∧
    (outerCount 55 j.val = 0 ∨ denominator 55 (outerCount 55 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (55+10)*(50+outerCount 55 j.val) := by decide

theorem row56_literal : ∀ j : Fin 90,
    (row56[j.val]! : ℤ) = roundedCumulative 56 j.val ∧
    (outerCount 56 j.val = 0 ∨ denominator 56 (outerCount 56 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (56+10)*(50+outerCount 56 j.val) := by decide

theorem row57_literal : ∀ j : Fin 90,
    (row57[j.val]! : ℤ) = roundedCumulative 57 j.val ∧
    (outerCount 57 j.val = 0 ∨ denominator 57 (outerCount 57 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (57+10)*(50+outerCount 57 j.val) := by decide

theorem row58_literal : ∀ j : Fin 90,
    (row58[j.val]! : ℤ) = roundedCumulative 58 j.val ∧
    (outerCount 58 j.val = 0 ∨ denominator 58 (outerCount 58 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (58+10)*(50+outerCount 58 j.val) := by decide

theorem row59_literal : ∀ j : Fin 90,
    (row59[j.val]! : ℤ) = roundedCumulative 59 j.val ∧
    (outerCount 59 j.val = 0 ∨ denominator 59 (outerCount 59 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (59+10)*(50+outerCount 59 j.val) := by decide

run_cmd Lean.logInfo "LITERAL RECTANGLES: submitting row block 60 through 69"

theorem row60_literal : ∀ j : Fin 90,
    (row60[j.val]! : ℤ) = roundedCumulative 60 j.val ∧
    (outerCount 60 j.val = 0 ∨ denominator 60 (outerCount 60 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (60+10)*(50+outerCount 60 j.val) := by decide

theorem row61_literal : ∀ j : Fin 90,
    (row61[j.val]! : ℤ) = roundedCumulative 61 j.val ∧
    (outerCount 61 j.val = 0 ∨ denominator 61 (outerCount 61 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (61+10)*(50+outerCount 61 j.val) := by decide

theorem row62_literal : ∀ j : Fin 90,
    (row62[j.val]! : ℤ) = roundedCumulative 62 j.val ∧
    (outerCount 62 j.val = 0 ∨ denominator 62 (outerCount 62 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (62+10)*(50+outerCount 62 j.val) := by decide

theorem row63_literal : ∀ j : Fin 90,
    (row63[j.val]! : ℤ) = roundedCumulative 63 j.val ∧
    (outerCount 63 j.val = 0 ∨ denominator 63 (outerCount 63 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (63+10)*(50+outerCount 63 j.val) := by decide

theorem row64_literal : ∀ j : Fin 90,
    (row64[j.val]! : ℤ) = roundedCumulative 64 j.val ∧
    (outerCount 64 j.val = 0 ∨ denominator 64 (outerCount 64 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (64+10)*(50+outerCount 64 j.val) := by decide

theorem row65_literal : ∀ j : Fin 90,
    (row65[j.val]! : ℤ) = roundedCumulative 65 j.val ∧
    (outerCount 65 j.val = 0 ∨ denominator 65 (outerCount 65 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (65+10)*(50+outerCount 65 j.val) := by decide

theorem row66_literal : ∀ j : Fin 90,
    (row66[j.val]! : ℤ) = roundedCumulative 66 j.val ∧
    (outerCount 66 j.val = 0 ∨ denominator 66 (outerCount 66 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (66+10)*(50+outerCount 66 j.val) := by decide

theorem row67_literal : ∀ j : Fin 90,
    (row67[j.val]! : ℤ) = roundedCumulative 67 j.val ∧
    (outerCount 67 j.val = 0 ∨ denominator 67 (outerCount 67 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (67+10)*(50+outerCount 67 j.val) := by decide

theorem row68_literal : ∀ j : Fin 90,
    (row68[j.val]! : ℤ) = roundedCumulative 68 j.val ∧
    (outerCount 68 j.val = 0 ∨ denominator 68 (outerCount 68 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (68+10)*(50+outerCount 68 j.val) := by decide

theorem row69_literal : ∀ j : Fin 90,
    (row69[j.val]! : ℤ) = roundedCumulative 69 j.val ∧
    (outerCount 69 j.val = 0 ∨ denominator 69 (outerCount 69 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (69+10)*(50+outerCount 69 j.val) := by decide

run_cmd Lean.logInfo "LITERAL RECTANGLES: submitting row block 70 through 79"

theorem row70_literal : ∀ j : Fin 90,
    (row70[j.val]! : ℤ) = roundedCumulative 70 j.val ∧
    (outerCount 70 j.val = 0 ∨ denominator 70 (outerCount 70 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (70+10)*(50+outerCount 70 j.val) := by decide

theorem row71_literal : ∀ j : Fin 90,
    (row71[j.val]! : ℤ) = roundedCumulative 71 j.val ∧
    (outerCount 71 j.val = 0 ∨ denominator 71 (outerCount 71 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (71+10)*(50+outerCount 71 j.val) := by decide

theorem row72_literal : ∀ j : Fin 90,
    (row72[j.val]! : ℤ) = roundedCumulative 72 j.val ∧
    (outerCount 72 j.val = 0 ∨ denominator 72 (outerCount 72 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (72+10)*(50+outerCount 72 j.val) := by decide

theorem row73_literal : ∀ j : Fin 90,
    (row73[j.val]! : ℤ) = roundedCumulative 73 j.val ∧
    (outerCount 73 j.val = 0 ∨ denominator 73 (outerCount 73 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (73+10)*(50+outerCount 73 j.val) := by decide

theorem row74_literal : ∀ j : Fin 90,
    (row74[j.val]! : ℤ) = roundedCumulative 74 j.val ∧
    (outerCount 74 j.val = 0 ∨ denominator 74 (outerCount 74 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (74+10)*(50+outerCount 74 j.val) := by decide

theorem row75_literal : ∀ j : Fin 90,
    (row75[j.val]! : ℤ) = roundedCumulative 75 j.val ∧
    (outerCount 75 j.val = 0 ∨ denominator 75 (outerCount 75 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (75+10)*(50+outerCount 75 j.val) := by decide

theorem row76_literal : ∀ j : Fin 90,
    (row76[j.val]! : ℤ) = roundedCumulative 76 j.val ∧
    (outerCount 76 j.val = 0 ∨ denominator 76 (outerCount 76 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (76+10)*(50+outerCount 76 j.val) := by decide

theorem row77_literal : ∀ j : Fin 90,
    (row77[j.val]! : ℤ) = roundedCumulative 77 j.val ∧
    (outerCount 77 j.val = 0 ∨ denominator 77 (outerCount 77 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (77+10)*(50+outerCount 77 j.val) := by decide

theorem row78_literal : ∀ j : Fin 90,
    (row78[j.val]! : ℤ) = roundedCumulative 78 j.val ∧
    (outerCount 78 j.val = 0 ∨ denominator 78 (outerCount 78 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (78+10)*(50+outerCount 78 j.val) := by decide

theorem row79_literal : ∀ j : Fin 90,
    (row79[j.val]! : ℤ) = roundedCumulative 79 j.val ∧
    (outerCount 79 j.val = 0 ∨ denominator 79 (outerCount 79 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (79+10)*(50+outerCount 79 j.val) := by decide

run_cmd Lean.logInfo "LITERAL RECTANGLES: submitting row block 80 through 89"

theorem row80_literal : ∀ j : Fin 90,
    (row80[j.val]! : ℤ) = roundedCumulative 80 j.val ∧
    (outerCount 80 j.val = 0 ∨ denominator 80 (outerCount 80 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (80+10)*(50+outerCount 80 j.val) := by decide

theorem row81_literal : ∀ j : Fin 90,
    (row81[j.val]! : ℤ) = roundedCumulative 81 j.val ∧
    (outerCount 81 j.val = 0 ∨ denominator 81 (outerCount 81 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (81+10)*(50+outerCount 81 j.val) := by decide

theorem row82_literal : ∀ j : Fin 90,
    (row82[j.val]! : ℤ) = roundedCumulative 82 j.val ∧
    (outerCount 82 j.val = 0 ∨ denominator 82 (outerCount 82 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (82+10)*(50+outerCount 82 j.val) := by decide

theorem row83_literal : ∀ j : Fin 90,
    (row83[j.val]! : ℤ) = roundedCumulative 83 j.val ∧
    (outerCount 83 j.val = 0 ∨ denominator 83 (outerCount 83 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (83+10)*(50+outerCount 83 j.val) := by decide

theorem row84_literal : ∀ j : Fin 90,
    (row84[j.val]! : ℤ) = roundedCumulative 84 j.val ∧
    (outerCount 84 j.val = 0 ∨ denominator 84 (outerCount 84 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (84+10)*(50+outerCount 84 j.val) := by decide

theorem row85_literal : ∀ j : Fin 90,
    (row85[j.val]! : ℤ) = roundedCumulative 85 j.val ∧
    (outerCount 85 j.val = 0 ∨ denominator 85 (outerCount 85 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (85+10)*(50+outerCount 85 j.val) := by decide

theorem row86_literal : ∀ j : Fin 90,
    (row86[j.val]! : ℤ) = roundedCumulative 86 j.val ∧
    (outerCount 86 j.val = 0 ∨ denominator 86 (outerCount 86 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (86+10)*(50+outerCount 86 j.val) := by decide

theorem row87_literal : ∀ j : Fin 90,
    (row87[j.val]! : ℤ) = roundedCumulative 87 j.val ∧
    (outerCount 87 j.val = 0 ∨ denominator 87 (outerCount 87 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (87+10)*(50+outerCount 87 j.val) := by decide

theorem row88_literal : ∀ j : Fin 90,
    (row88[j.val]! : ℤ) = roundedCumulative 88 j.val ∧
    (outerCount 88 j.val = 0 ∨ denominator 88 (outerCount 88 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (88+10)*(50+outerCount 88 j.val) := by decide

theorem row89_literal : ∀ j : Fin 90,
    (row89[j.val]! : ℤ) = roundedCumulative 89 j.val ∧
    (outerCount 89 j.val = 0 ∨ denominator 89 (outerCount 89 j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (89+10)*(50+outerCount 89 j.val) := by decide

theorem forces_literal : ∀ i : Fin 90,
    (forces[i.val]! : ℤ) = roundedForcing i.val ∧
    (forcingCount i.val = 0 ∨ denominator i.val (forcingCount i.val-1) ≤ 750) ∧
    1000 ≤ (i.val+10)*(50+forcingCount i.val) := by decide

theorem all_rows_literal : ∀ i j : Fin 90,
    ((matrix[i.val]!)[j.val]! : ℤ) = roundedCumulative i.val j.val ∧
    (outerCount i.val j.val = 0 ∨ denominator i.val (outerCount i.val j.val - 1) ≤ 50*(j.val+16)) ∧
    50*(j.val+21) ≤ (i.val+10)*(50+outerCount i.val j.val) := by
  intro i
  fin_cases i
  · exact row0_literal
  · exact row1_literal
  · exact row2_literal
  · exact row3_literal
  · exact row4_literal
  · exact row5_literal
  · exact row6_literal
  · exact row7_literal
  · exact row8_literal
  · exact row9_literal
  · exact row10_literal
  · exact row11_literal
  · exact row12_literal
  · exact row13_literal
  · exact row14_literal
  · exact row15_literal
  · exact row16_literal
  · exact row17_literal
  · exact row18_literal
  · exact row19_literal
  · exact row20_literal
  · exact row21_literal
  · exact row22_literal
  · exact row23_literal
  · exact row24_literal
  · exact row25_literal
  · exact row26_literal
  · exact row27_literal
  · exact row28_literal
  · exact row29_literal
  · exact row30_literal
  · exact row31_literal
  · exact row32_literal
  · exact row33_literal
  · exact row34_literal
  · exact row35_literal
  · exact row36_literal
  · exact row37_literal
  · exact row38_literal
  · exact row39_literal
  · exact row40_literal
  · exact row41_literal
  · exact row42_literal
  · exact row43_literal
  · exact row44_literal
  · exact row45_literal
  · exact row46_literal
  · exact row47_literal
  · exact row48_literal
  · exact row49_literal
  · exact row50_literal
  · exact row51_literal
  · exact row52_literal
  · exact row53_literal
  · exact row54_literal
  · exact row55_literal
  · exact row56_literal
  · exact row57_literal
  · exact row58_literal
  · exact row59_literal
  · exact row60_literal
  · exact row61_literal
  · exact row62_literal
  · exact row63_literal
  · exact row64_literal
  · exact row65_literal
  · exact row66_literal
  · exact row67_literal
  · exact row68_literal
  · exact row69_literal
  · exact row70_literal
  · exact row71_literal
  · exact row72_literal
  · exact row73_literal
  · exact row74_literal
  · exact row75_literal
  · exact row76_literal
  · exact row77_literal
  · exact row78_literal
  · exact row79_literal
  · exact row80_literal
  · exact row81_literal
  · exact row82_literal
  · exact row83_literal
  · exact row84_literal
  · exact row85_literal
  · exact row86_literal
  · exact row87_literal
  · exact row88_literal
  · exact row89_literal

theorem cumulative_bound (i j : Fin 90) :
    cumulativeRectangles i.val j.val ≤ ((matrix[i.val]!)[j.val]! : ℝ)/scale := by
  obtain ⟨he, ha, _⟩ := all_rows_literal i j
  have h := cumulative_rectangles_le i.val j.val (active_of_last i.val j.val ha)
  rw [← he] at h
  simpa only [Int.cast_natCast] using h

theorem forcing_bound (i : Fin 90) :
    forcingRectangles i.val ≤ (forces[i.val]! : ℝ)/scale := by
  have h := forcing_rectangles_le i.val
  rw [← (forces_literal i).1] at h
  simpa only [Int.cast_natCast] using h

run_cmd do
  for decl in [``row0_literal, ``row1_literal, ``row2_literal, ``row3_literal, ``row4_literal, ``row5_literal, ``row6_literal, ``row7_literal, ``row8_literal, ``row9_literal, ``row10_literal, ``row11_literal, ``row12_literal, ``row13_literal, ``row14_literal, ``row15_literal, ``row16_literal, ``row17_literal, ``row18_literal, ``row19_literal, ``row20_literal, ``row21_literal, ``row22_literal, ``row23_literal, ``row24_literal, ``row25_literal, ``row26_literal, ``row27_literal, ``row28_literal, ``row29_literal, ``row30_literal, ``row31_literal, ``row32_literal, ``row33_literal, ``row34_literal, ``row35_literal, ``row36_literal, ``row37_literal, ``row38_literal, ``row39_literal, ``row40_literal, ``row41_literal, ``row42_literal, ``row43_literal, ``row44_literal, ``row45_literal, ``row46_literal, ``row47_literal, ``row48_literal, ``row49_literal, ``row50_literal, ``row51_literal, ``row52_literal, ``row53_literal, ``row54_literal, ``row55_literal, ``row56_literal, ``row57_literal, ``row58_literal, ``row59_literal, ``row60_literal, ``row61_literal, ``row62_literal, ``row63_literal, ``row64_literal, ``row65_literal, ``row66_literal, ``row67_literal, ``row68_literal, ``row69_literal, ``row70_literal, ``row71_literal, ``row72_literal, ``row73_literal, ``row74_literal, ``row75_literal, ``row76_literal, ``row77_literal, ``row78_literal, ``row79_literal, ``row80_literal, ``row81_literal, ``row82_literal, ``row83_literal, ``row84_literal, ``row85_literal, ``row86_literal, ``row87_literal, ``row88_literal, ``row89_literal, ``forces_literal, ``all_rows_literal, ``cumulative_bound, ``forcing_bound] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL RATIONAL RECTANGLE TABLES: STANDARD AXIOMS ONLY"
end ProfileCertificateRectangleTables
