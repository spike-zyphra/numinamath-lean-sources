import Mathlib

open Real

theorem inequalities_325151 (a : ℝ) :
    (∀ x y : ℝ, x > 0 → y > 0 → x + 2 * sqrt (2 * x * y) ≤ a * (x + y)) ↔ a ≥ 2 := by
  constructor
  · -- Assume inequality holds, prove a ≥ 2
    intro h
    have h1 := h 2 1 (by norm_num) (by norm_num)
    have h2 : (2 : ℝ) + 2 * sqrt (2 * (2 : ℝ) * (1 : ℝ)) ≤ a * (2 + 1) := by
      simpa using h1
    have h3 : sqrt (2 * (2 : ℝ) * (1 : ℝ)) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h3] at h2
    nlinarith
  · -- Assume a ≥ 2, prove the inequality
    intro ha x y hx hy
    have h2 : x + 2 * sqrt (2 * x * y) ≤ 2 * (x + y) := by
      have h3 : 2 * sqrt (2 * x * y) ≤ x + 2 * y := by
        have h4 : (2 * sqrt (2 * x * y)) ^ 2 ≤ (x + 2 * y) ^ 2 := by
          have h5 : (2 * sqrt (2 * x * y)) ^ 2 = 8 * x * y := by
            calc
              (2 * sqrt (2 * x * y)) ^ 2 = 4 * (sqrt (2 * x * y) ^ 2) := by ring_nf
              _ = 4 * (2 * x * y) := by
                have h6 : 2 * x * y > 0 := by
                  apply mul_pos
                  apply mul_pos
                  all_goals linarith
                rw [Real.sq_sqrt (by nlinarith)]
              _ = 8 * x * y := by ring
          have h6 : (x + 2 * y) ^ 2 = x^2 + 4 * x * y + 4 * y^2 := by
            ring
          have h7 : x^2 + 4 * x * y + 4 * y^2 ≥ 8 * x * y := by
            nlinarith [sq_nonneg (x - 2 * y)]
          nlinarith [h6, h7]
        have h8 : (2 * sqrt (2 * x * y)) ≥ 0 := by
          positivity
        have h9 : (x + 2 * y) ≥ 0 := by
          nlinarith
        nlinarith [sq_nonneg (2 * sqrt (2 * x * y) - (x + 2 * y)), Real.sqrt_nonneg (2 * x * y)]
      nlinarith
    have h3 : a * (x + y) ≥ 2 * (x + y) := by
      nlinarith
    linarith [h2, h3]