import Mathlib

theorem algebra_1569 {x : ℝ} (hx : x = 2 - √5) : x^4 - 8 * x^3 + 16 * x^2 - x + 1 = √5 := by
  have h1 : x = 2 - Real.sqrt 5 := by
    exact hx
  have h2 : x^2 - 4 * x - 1 = 0 := by
    rw [h1]
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (5 : ℝ)), Real.sqrt_nonneg 5]
  have h21 : x^2 = 4 * x + 1 := by 
    linarith
  have h22 : x^3 = 17 * x + 4 := by 
    calc
      x^3 = x * x^2 := by ring
      _ = x * (4 * x + 1) := by rw [h21]
      _ = 4 * x^2 + x := by ring
      _ = 4 * (4 * x + 1) + x := by rw [h21]
      _ = 17 * x + 4 := by ring
  have h23 : x^4 = 72 * x + 17 := by 
    calc
      x^4 = x * x^3 := by ring
      _ = x * (17 * x + 4) := by rw [h22]
      _ = 17 * x^2 + 4 * x := by ring
      _ = 17 * (4 * x + 1) + 4 * x := by rw [h21]
      _ = 72 * x + 17 := by ring
  calc
    x^4 - 8 * x^3 + 16 * x^2 - x + 1 
        = (72 * x + 17) - 8 * (17 * x + 4) + 16 * (4 * x + 1) - x + 1 := by 
          rw [show x^4 = 72 * x + 17 by linarith [h23]]
          rw [show x^3 = 17 * x + 4 by linarith [h22]]
          rw [show x^2 = 4 * x + 1 by linarith [h21]]
          <;> ring
    _ = -x + 2 := by ring
    _ = Real.sqrt 5 := by 
      rw [show x = 2 - Real.sqrt 5 by exact hx]
      ring_nf
      <;> norm_num