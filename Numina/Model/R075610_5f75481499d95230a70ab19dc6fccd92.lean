import Mathlib

theorem algebra_271354 {x : ℝ} (hx : x = Real.sqrt (19 - 8 * Real.sqrt 3)) :
    (x ^ 4 - 6 * x ^ 3 - 2 * x ^ 2 + 18 * x + 23) / (x ^ 2 - 8 * x + 15) = 5 := by
  have h1 : x = 4 - Real.sqrt 3 := by
    rw [hx]
    have h2 : Real.sqrt (19 - 8 * Real.sqrt 3) = 4 - Real.sqrt 3 := by
      have h3 : (4 - Real.sqrt 3) ^ 2 = 19 - 8 * Real.sqrt 3 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
      have h4 : 0 ≤ (4 - Real.sqrt 3 : ℝ) := by
        have h5 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
        have h6 : Real.sqrt 3 ≤ (4 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
        nlinarith
      rw [← h3]
      field_simp [h4, Real.sqrt_nonneg (19 - 8 * Real.sqrt 3)]
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (19 - 8 * Real.sqrt 3)]
    linarith [h2]
  
  have h8 : x ^ 2 - 8 * x + 13 = 0 := by
    rw [h1]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (3)]

  have h3 : x ^ 2 = 8 * x - 13 := by linarith

  have h4 : x ^ 3 = 51 * x - 104 := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = x * (8 * x - 13) := by rw [h3]
      _ = 8 * x ^ 2 - 13 * x := by ring
      _ = 8 * (8 * x - 13) - 13 * x := by rw [h3]
      _ = 51 * x - 104 := by ring

  have h5 : x ^ 4 = 304 * x - 663 := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = (8 * x - 13) ^ 2 := by rw [h3]
      _ = 64 * (x ^ 2) - 208 * x + 169 := by ring
      _ = 64 * (8 * x - 13) - 208 * x + 169 := by rw [h3]
      _ = 304 * x - 663 := by ring
  
  have h6 : x ^ 4 - 6 * x ^ 3 - 2 * x ^ 2 + 18 * x + 23 = 10 := by
    rw [h5, h4, h3]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (3)]

  have h7 : x ^ 2 - 8 * x + 15 = 2 := by
    have h8 : x ^ 2 - 8 * x = -13 := by linarith
    linarith

  rw [h6, h7]
  all_goals norm_num