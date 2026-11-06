import Mathlib

theorem algebra_94316 {r : ℝ} (hr : r ≠ 0) (h : r + 1 / r = Real.sqrt 3 ∨ r + 1 / r = -Real.sqrt 3) :
    r ^ 3 + 1 / r ^ 3 = 0 := by
  rcases h with (h | h)
  · -- Assume r + 1/r = Real.sqrt 3
    have h1 : r + 1 / r = Real.sqrt 3 := h
    have eq1 : r ^ 3 + 1 / r ^ 3 = (r + 1 / r) ^ 3 - 3 * (r + 1 / r) := by
      field_simp [hr]
      ring
    rw [eq1, h1]
    have h2 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h3 : (Real.sqrt 3 : ℝ) ^ 3 = (Real.sqrt 3) * 3 := by
      calc
        (Real.sqrt 3 : ℝ) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
        _ = 3 * Real.sqrt 3 := by rw [h2]
        _ = Real.sqrt 3 * 3 := by ring
    rw [h3]
    ring
  · -- Assume r + 1/r = -Real.sqrt 3
    have h1 : r + 1 / r = -Real.sqrt 3 := h
    have eq1 : r ^ 3 + 1 / r ^ 3 = (r + 1 / r) ^ 3 - 3 * (r + 1 / r) := by
      field_simp [hr]
      ring
    rw [eq1, h1]
    have h2 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h3 : (Real.sqrt 3 : ℝ) ^ 3 = (Real.sqrt 3) * 3 := by
      calc
        (Real.sqrt 3 : ℝ) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
        _ = 3 * Real.sqrt 3 := by rw [h2]
        _ = Real.sqrt 3 * 3 := by ring
    have h4 : (- (Real.sqrt 3 : ℝ)) ^ 3 = - ( (Real.sqrt 3 : ℝ) ^ 3 ) := by ring
    rw [h4, h3]
    ring