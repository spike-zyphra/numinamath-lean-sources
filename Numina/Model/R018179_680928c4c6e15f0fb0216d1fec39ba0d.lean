import Mathlib

open Real

theorem number_theory_307737 {a b : ℝ} (ha : a = sqrt 3 - ⌊sqrt 3⌋) (hb : b = sqrt 2 - ⌊sqrt 2⌋) :
    ⌊(a / ((a - b) * b))⌋ = 5 := by
  have ha1 : ⌊sqrt 3⌋ = 1 := by 
    have h1 : 1 < sqrt 3 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h2 : sqrt 3 < 2 := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have hb1 : ⌊sqrt 2⌋ = 1 := by 
    have h1 : 1 < sqrt 2 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h2 : sqrt 2 < 2 := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have ha2 : a = Real.sqrt 3 - 1 := by 
    rw [ha, ha1]
    all_goals norm_num
  have hb2 : b = Real.sqrt 2 - 1 := by
    rw [hb, hb1]
    all_goals norm_num
  rw [ha2, hb2]
  have h1 : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt] <;> norm_num
  have h3 : 1 < Real.sqrt 3 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h4 : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt] <;> norm_num
  have h5 : 0 < Real.sqrt 2 - 1 := by
    linarith
  have h6 : 0 < Real.sqrt 3 - 1 := by
    linarith
  have h7 : 0 < Real.sqrt 3 - Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have pos1 : 0 < (Real.sqrt 3 - Real.sqrt 2) * (Real.sqrt 2 - 1) := by
    positivity
  have h10 : 5 ≤ (Real.sqrt 3 - 1) / ((Real.sqrt 3 - Real.sqrt 2) * (Real.sqrt 2 - 1)) := by
    apply (le_div_iff₀ pos1).mpr
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (Real.sqrt 2 ^ 2 - 2), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - Real.sqrt 2), sq_nonneg (Real.sqrt 3 - 2), sq_nonneg (Real.sqrt 2 - 1), Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)]
  have h11 : (Real.sqrt 3 - 1) / ((Real.sqrt 3 - Real.sqrt 2) * (Real.sqrt 2 - 1)) < 6 := by
    apply (div_lt_iff₀ pos1).mpr
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (Real.sqrt 2 ^ 2 - 2), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - Real.sqrt 2), sq_nonneg (Real.sqrt 3 - 2), sq_nonneg (Real.sqrt 2 - 1), Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> nlinarith