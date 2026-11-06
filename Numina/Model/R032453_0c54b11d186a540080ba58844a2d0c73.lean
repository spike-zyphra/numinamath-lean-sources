import Mathlib

theorem algebra_280509 (x : ℝ) (hx : 5 * x - 9 ≥ 0 ∧ 3 * x - 5 ≥ 0) :
    Real.sqrt (15 * x ^ 2 - 52 * x + 45) * (3 - Real.sqrt (5 * x - 9) - Real.sqrt (3 * x - 5)) = 1 ↔ x = 2 := by
  constructor
  · -- Forward direction: the equation implies x = 2.
    intro h_eq
    have h1 : 5 * x - 9 ≥ 0 := hx.1
    have h2 : 3 * x - 5 ≥ 0 := hx.2
    have h3 : 15 * x ^ 2 - 52 * x + 45 = (5 * x - 9) * (3 * x - 5) := by
      nlinarith
    have h4 : Real.sqrt (15 * x ^ 2 - 52 * x + 45) = Real.sqrt (5 * x - 9) * Real.sqrt (3 * x - 5) := by
      rw [h3]
      <;> try { 
        rw [Real.sqrt_mul]
        all_goals
        nlinarith
      }
    rw [h4] at h_eq
    have h7 : Real.sqrt (5 * x - 9) = 1 := by
      nlinarith [Real.sqrt_nonneg (5 * x - 9), Real.sqrt_nonneg (3 * x - 5),
        mul_nonneg (Real.sqrt_nonneg (5 * x - 9)) (Real.sqrt_nonneg (3 * x - 5)), 
        sq_nonneg (Real.sqrt (5 * x - 9) - 1), 
        sq_nonneg (Real.sqrt (3 * x - 5) - 1), 
        Real.sq_sqrt (show 0 ≤ (5 * x - 9 : ℝ) by linarith), 
        Real.sq_sqrt (show 0 ≤ (3 * x - 5 : ℝ) by linarith), 
        sq_nonneg (Real.sqrt (5 * x - 9) ^ 2 - (1 : ℝ)), 
        sq_nonneg (Real.sqrt (3 * x - 5) ^ 2 - (1 : ℝ)), 
        mul_nonneg (show 0 ≤ (5 * x - 9 : ℝ) by linarith) (show 0 ≤ (3 * x - 5 : ℝ) by linarith), 
        h_eq 
      ]
    -- From sqrt(a) = 1 derive a = 1.

    have h8 : 5 * x - 9 = 1 := by
      calc
        5 * x - 9 = Real.sqrt (5 * x - 9) ^ 2 := by rw [Real.sq_sqrt]; linarith
        _ = 1 ^ 2 := by rw [h7]
        _ = 1 := by norm_num
    -- Now solve for x.

    have h9 : x = 2 := by
      nlinarith
    assumption
  · -- Backward direction: x = 2 implies the equation.
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (15 * (2 : ℝ) ^ 2 - 52 * (2 : ℝ) + 45) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (5 * (2 : ℝ) - 9) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt (3 * (2 : ℝ) - 5) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3]
    all_goals norm_num