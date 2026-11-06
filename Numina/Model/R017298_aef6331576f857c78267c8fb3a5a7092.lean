import Mathlib

theorem algebra_166453 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x * Real.sqrt y + y * Real.sqrt x = 30) (h2 : x * Real.sqrt x + y * Real.sqrt y = 35) :
    (x, y) = (4, 9) ∨ (x, y) = (9, 4) := by
  have h3 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have h4 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  have h5 : Real.sqrt x > 0 := by positivity
  have h6 : Real.sqrt y > 0 := by positivity
  have eq1 : Real.sqrt x ^ 2 * Real.sqrt y + Real.sqrt y ^ 2 * Real.sqrt x = 30 := by
    have h7 : x * Real.sqrt y + y * Real.sqrt x = 30 := h1
    have eq1' : Real.sqrt x ^ 2 * Real.sqrt y + Real.sqrt y ^ 2 * Real.sqrt x = x * Real.sqrt y + y * Real.sqrt x := by
      have h8 : Real.sqrt x ^ 2 = x := by linarith [h3]
      have h9 : Real.sqrt y ^ 2 = y := by linarith [h4]
      rw [h8, h9]
      all_goals linarith
    linarith [eq1', h7]
  have eq2 : Real.sqrt x ^ 3 + Real.sqrt y ^ 3 = 35 := by
    have h8 : x * Real.sqrt x = Real.sqrt x ^ 3 := by
      have h9 : Real.sqrt x ^ 2 = x := by linarith [h3]
      nlinarith
    have h10 : y * Real.sqrt y = Real.sqrt y ^ 3 := by
      have h11 : Real.sqrt y ^ 2 = y := by linarith [h4]
      nlinarith
    have h7 : x * Real.sqrt x + y * Real.sqrt y = 35 := h2
    linarith [h7, h8, h10]
  have eq3 : Real.sqrt x * Real.sqrt y * (Real.sqrt x + Real.sqrt y) = 30 := by
    nlinarith [eq1, sq_pos_of_pos h5, sq_pos_of_pos h6, mul_pos h5 h6]
  have eq4 : (Real.sqrt x + Real.sqrt y) ^ 3 - 3 * (Real.sqrt x * Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = 35 := by
    nlinarith [eq2, sq_pos_of_pos h5, sq_pos_of_pos h6, mul_pos h5 h6]
  have eq5 : (Real.sqrt x + Real.sqrt y) ^ 3 = 125 := by
    nlinarith [eq3, eq4, sq_pos_of_pos h5, sq_pos_of_pos h6, mul_pos h5 h6]
  have hS : Real.sqrt x + Real.sqrt y = 5 := by
    have h1 : (Real.sqrt x + Real.sqrt y) ^ 3 = 125 := eq5
    have h2 : Real.sqrt x + Real.sqrt y > 0 := by positivity
    have h3 : Real.sqrt x + Real.sqrt y = 5 := by
      have h4 : (Real.sqrt x + Real.sqrt y) ^ 3 - 125 = 0 := by linarith
      have h5 : (Real.sqrt x + Real.sqrt y - 5) * ((Real.sqrt x + Real.sqrt y) ^ 2 + 5 * (Real.sqrt x + Real.sqrt y) + 25) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h5) with h6 h7
      · linarith
      · -- Let's prove that quadratic has no real solution.
        nlinarith [sq_nonneg (Real.sqrt x + Real.sqrt y + 5 / 2)]
    linarith
  have hP : Real.sqrt x * Real.sqrt y = 6 := by
    nlinarith [eq3, hS, sq_pos_of_pos h5, sq_pos_of_pos h6]
  have h8 : (Real.sqrt x - 2) * (Real.sqrt x - 3) = 0 := by
    have h1 : Real.sqrt x + Real.sqrt y = 5 := hS
    have h2 : Real.sqrt x * Real.sqrt y = 6 := hP
    have h3 : Real.sqrt y = 5 - Real.sqrt x := by linarith
    rw [h3] at h2
    nlinarith [sq_nonneg (Real.sqrt x - 2), sq_nonneg (Real.sqrt x - 3)]
  cases' (mul_eq_zero.1 h8) with h9 h10
  · -- Real.sqrt x = 2
    have hx2 : Real.sqrt x = 2 := by linarith
    have hx4 : x = 4 := by
      calc
        x = Real.sqrt x ^ 2 := by linarith [h3]
        _ = (2 : ℝ) ^ 2 := by rw [hx2]
        _ = (4 : ℝ) := by norm_num
    have h1y : Real.sqrt y = 3 := by nlinarith [hS, hx2]
    have hy9 : y = 9 := by
      calc
        y = Real.sqrt y ^ 2 := by linarith [h4]
        _ = (3 : ℝ) ^ 2 := by rw [h1y]
        _ = (9 : ℝ) := by norm_num
    left
    simp [Prod.ext_iff, hx4, hy9]
  · -- Real.sqrt x = 3
    have hx3 : Real.sqrt x = 3 := by linarith
    have hx9 : x = 9 := by
      calc
        x = Real.sqrt x ^ 2 := by linarith [h3]
        _ = (3 : ℝ) ^ 2 := by rw [hx3]
        _ = (9 : ℝ) := by norm_num
    have h1y : Real.sqrt y = 2 := by nlinarith [hS, hx3]
    have hy4 : y = 4 := by
      calc
        y = Real.sqrt y ^ 2 := by linarith [h4]
        _ = (2 : ℝ) ^ 2 := by rw [h1y]
        _ = (4 : ℝ) := by norm_num
    right
    simp [Prod.ext_iff, hx9, hy4]