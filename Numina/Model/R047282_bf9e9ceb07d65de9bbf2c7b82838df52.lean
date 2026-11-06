import Mathlib

theorem algebra_119092 : ⌊(Real.sqrt 3 + 1)^6⌋ = 415 := by 
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 3 ^ 3 = Real.sqrt 3 * 3 := by 
    calc
      Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [h1]
      _ = Real.sqrt 3 * 3 := by ring 
  have h3 : Real.sqrt 3 ^ 4 = (9 : ℝ) := by
    calc
      Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = (3) ^ 2 := by rw [h1]
      _ = (9 : ℝ) := by norm_num 
  have h6 : Real.sqrt 3 ^ 6 = (27 : ℝ) := by 
    calc
      Real.sqrt 3 ^ 6 = Real.sqrt 3 ^ 4 * Real.sqrt 3 ^ 2 := by ring
      _ = (9 : ℝ) * (3 : ℝ) := by 
        rw [h3, h1]
      _ = (27 : ℝ) := by norm_num 
  have h7 : (Real.sqrt 3 + 1) ^ 6 = (208 : ℝ) + 120 * Real.sqrt 3 := by 
    ring_nf 
    nlinarith [h1, h2, h3, h6, sq_nonneg (Real.sqrt 3 - 1)]
  rw [h7]
  have h10 : (1.732 : ℝ) < Real.sqrt 3 := by 
    nlinarith [Real.sqrt_nonneg (3), h1, sq_nonneg (Real.sqrt 3 - 1.732)]
  have h11 : Real.sqrt 3 < (1.733 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (3), h1, sq_nonneg (Real.sqrt 3 - 1.733)]
  have h12 : (208 : ℝ) + 120 * Real.sqrt 3 > (415 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (3), h10, Real.sq_sqrt (show (0 : ℝ) ≤ (3: ℝ) by norm_num)]
  have h13 : (208 : ℝ) + 120 * Real.sqrt 3 < (416 : ℝ) := by 
    nlinarith [Real.sqrt_nonneg (3), h11, Real.sq_sqrt (show (0 : ℝ) ≤ (3: ℝ) by norm_num)]
  have h14 : ⌊((208 : ℝ) + 120 * Real.sqrt 3)⌋ = 415 := by 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith [Real.sqrt_nonneg (3)]
  exact_mod_cast h14