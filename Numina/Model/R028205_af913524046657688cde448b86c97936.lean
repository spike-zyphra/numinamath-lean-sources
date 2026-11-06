import Mathlib

theorem algebra_103346 :
    ∃ n : ℕ, Real.sqrt (9 - Real.sqrt 77) * Real.sqrt 2 * (Real.sqrt 11 - Real.sqrt 7) * (9 + Real.sqrt 77) = n ∧
    ∀ x y : ℝ, x * y = 6 → x > 2 → y > 2 → x + y < 5 := by

  use 8
  constructor
  · -- Show the given expression equals 8
    have h1 : Real.sqrt (9 - Real.sqrt 77) * Real.sqrt 2 = Real.sqrt 11 - Real.sqrt 7 := by
      have h2 : (Real.sqrt (9 - Real.sqrt 77) * Real.sqrt 2) ^ 2 = (Real.sqrt 11 - Real.sqrt 7) ^ 2 := by
        have h2a : Real.sqrt (9 - Real.sqrt 77) ^ 2 = 9 - Real.sqrt 77 := by
          rw [Real.sq_sqrt]
          have : (9 - Real.sqrt 77) ≥ 0 := by
            nlinarith [Real.sqrt_nonneg 77, Real.sq_sqrt (show (0 : ℝ) ≤ 77 by norm_num), sq_nonneg (Real.sqrt 77 - 9)]
          linarith
        have h4a : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
        have h4b : (Real.sqrt (9 - Real.sqrt 77) * Real.sqrt 2) ^ 2 = Real.sqrt (9 - Real.sqrt 77) ^ 2 * Real.sqrt 2 ^ 2 := by ring
        rw [h4b, h2a, h4a]
        have h7a : (Real.sqrt 11 - Real.sqrt 7) ^ 2 = 18 - 2 * Real.sqrt 77 := by
          have h8a : Real.sqrt 11 ^ 2 = (11 : ℝ) := Real.sq_sqrt (by norm_num)
          have h9a : Real.sqrt 7 ^ 2 = (7 : ℝ) := Real.sq_sqrt (by norm_num)
          have h10a : Real.sqrt 77 = Real.sqrt 11 * Real.sqrt 7 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            <;> ring_nf <;> norm_num
          nlinarith [Real.sqrt_nonneg 11, Real.sqrt_nonneg 7, Real.sqrt_nonneg 77, h10a]
        nlinarith [h7a, Real.sqrt_nonneg 11, Real.sqrt_nonneg 7, Real.sqrt_nonneg 77, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (77 : ℝ) by norm_num)]
      have h9a : Real.sqrt (9 - Real.sqrt 77) * Real.sqrt 2 ≥ 0 := by
        positivity
      have h10a : Real.sqrt 11 - Real.sqrt 7 ≥ 0 := by
        have h11a : Real.sqrt 11 ≥ Real.sqrt 7 := Real.sqrt_le_sqrt (by norm_num)
        nlinarith [h11a, Real.sqrt_nonneg 11, Real.sqrt_nonneg 7]
      nlinarith [h2, h9a, h10a]
    have h4 : Real.sqrt (9 - Real.sqrt 77) * Real.sqrt 2 * (Real.sqrt 11 - Real.sqrt 7) * (9 + Real.sqrt 77) = (8 : ℝ) := by
      rw [show Real.sqrt (9 - Real.sqrt 77) * Real.sqrt 2 = Real.sqrt 11 - Real.sqrt 7 by linarith [h1]]
      have h77 : Real.sqrt 77 = Real.sqrt 11 * Real.sqrt 7 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      nlinarith [Real.sqrt_nonneg 11, Real.sqrt_nonneg 7, Real.sqrt_nonneg 77, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (77 : ℝ) by norm_num), sq_nonneg (Real.sqrt 11 ^ 2 - Real.sqrt 7 ^ 2), sq_nonneg (Real.sqrt 11 * Real.sqrt 7), sq_nonneg (Real.sqrt 77 - 8), Real.sqrt_nonneg 11, Real.sqrt_nonneg 7, Real.sqrt_nonneg 77]
    norm_num at h4 ⊢
    all_goals linarith
  · -- Prove the inequality
    intro x y hxy hx hy
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x * y - 6), mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy), sq_nonneg (x - y), sq_nonneg ((x + y) - 4)]