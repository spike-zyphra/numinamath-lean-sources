import Mathlib

theorem algebra_191302 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : 1 / x + 1 / y + 1 / (x * y) = 1) :
    x + y < -1 ∨ -1 < x + y ∧ x + y ≤ 2 - 2 * Real.sqrt 2 ∨ 2 - 2 * Real.sqrt 2 < x + y ∨
    x + y ≥ 2 + 2 * Real.sqrt 2 ∨ 2 + 2 * Real.sqrt 2 < x + y := by

  have h1 : x + y + 1 = x * y := by
    have h2 : x * y ≠ 0 := mul_ne_zero hx hy
    field_simp [hx, hy, h2] at h ⊢
    linarith

  have h2 : (x + y) ^ 2 - 4 * (x * y) ≥ 0 := by 
    nlinarith [sq_nonneg (x - y)]

  have h3 : x * y = (x + y) + 1 := by linarith [h1]

  have h4 : (x + y) ^ 2 - 4 * ((x + y) + 1) ≥ 0 := by
    rw [show x * y = (x + y) + 1 by linarith [h1]] at h2
    linarith

  by_cases h6 : (x + y) ≤ 2 - 2 * Real.sqrt 2
  · -- Case1: x + y ≤ 2 - 2 * Real.sqrt 2
    by_cases h7 : (x + y) < -1
    · -- Case1a: x + y < -1
      left 
      linarith
    · -- Case1b: x + y ≥ -1
      have h8 : -1 ≤ (x + y) := by linarith 
      have h9 : -1 < (x + y) := by
        by_contra h10 
        push_neg at h10 
        have h11 : (x + y) = -1 := by nlinarith 
        have h12 : x * y = 0 := by
          have h13 : x * y = (x + y) + 1 := by linarith [h1]
          rw [h11] at h13 
          linarith 
        cases' (mul_eq_zero.1 h12) with h14 h15 
        · -- x = 0
          contradiction 
        · -- y = 0 
          contradiction 
      right 
      left 
      constructor 
      · -- Show -1 < x + y 
        linarith 
      · -- Show x + y ≤ 2 - 2 * Real.sqrt 2 
        linarith 
  · -- Case2: x + y > 2 - 2 * Real.sqrt 2 
    have h7 : (x + y) > 2 - 2 * Real.sqrt 2 := by linarith 
    by_cases h8 : (x + y) ≥ 2 + 2 * Real.sqrt 2 
    · -- Case2a: x + y ≥ 2 + 2 * Real.sqrt 2 
      right 
      right 
      right 
      left 
      linarith 
    · -- Case2b: x + y < 2 + 2 * Real.sqrt 2 
      have h9 : (x + y) < 2 + 2 * Real.sqrt 2 := by linarith 
      have h10 : (x + y) ^ 2 - 4 * ((x + y) + 1) ≥ 0 := h4 
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
          Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2)]