import Mathlib
theorem algebra_605429 : IsGreatest {y : ℝ | ∃ x, y = |√(x ^ 2 + 4 * x + 8) - √(x ^ 2 + 8 * x + 17)|} (√5):= by
  constructor
  · -- Show that √5 is in the set.
    use -6
    have h1 : Real.sqrt ((-6 : ℝ) ^ 2 + 4 * (-6) + 8) = Real.sqrt 20 := by norm_num
    have h2 : Real.sqrt ((-6 : ℝ) ^ 2 + 8 * (-6) + 17) = Real.sqrt 5 := by norm_num
    rw [h1, h2]
    have h3 : Real.sqrt 20 = 2 * Real.sqrt 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h3]
    have h4 : (2 * Real.sqrt 5 - Real.sqrt 5 : ℝ) = Real.sqrt 5 := by linarith
    rw [show 2 * Real.sqrt 5 - Real.sqrt 5 = Real.sqrt 5 by linarith]
    norm_num [abs_of_nonneg]
  · -- Show that √5 is the greatest element in the set.
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : Real.sqrt (x ^ 2 + 4 * x + 8) = Real.sqrt ((x + 2) ^ 2 + 4) := by ring_nf
    have h2 : Real.sqrt (x ^ 2 + 8 * x + 17) = Real.sqrt ((x + 4) ^ 2 + 1) := by ring_nf
    rw [h1, h2] at hx
    have h3 : |Real.sqrt ((x + 2) ^ 2 + 4) - Real.sqrt ((x + 4) ^ 2 + 1)| ≤ Real.sqrt 5 := by
      have h4 : (Real.sqrt ((x + 2) ^ 2 + 4) - Real.sqrt ((x + 4) ^ 2 + 1)) ^ 2 ≤ 5 := by
        nlinarith [Real.sqrt_nonneg ((x + 2) ^ 2 + 4), Real.sqrt_nonneg ((x + 4) ^ 2 + 1), 
            Real.sq_sqrt (show 0 ≤ (x + 2) ^ 2 + 4 by nlinarith), 
            Real.sq_sqrt (show 0 ≤ (x + 4) ^ 2 + 1 by nlinarith), 
            sq_nonneg (Real.sqrt ((x + 2) ^ 2 + 4) - Real.sqrt ((x + 4) ^ 2 + 1) - Real.sqrt 5), 
            sq_nonneg ((x + 6) : ℝ), 
            mul_nonneg (Real.sqrt_nonneg ((x + 2) ^ 2 + 4)) (Real.sqrt_nonneg ((x + 4) ^ 2 + 1)), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
            Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
            ]
      have h3 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
      have h6 : Real.sqrt ((Real.sqrt ((x + 2) ^ 2 + 4) - Real.sqrt ((x + 4) ^ 2 + 1)) ^ 2) ≤ Real.sqrt 5 := by
        apply Real.sqrt_le_sqrt
        nlinarith
      have h7 : Real.sqrt ((Real.sqrt ((x + 2) ^ 2 + 4) - Real.sqrt ((x + 4) ^ 2 + 1)) ^ 2) = |Real.sqrt ((x + 2) ^ 2 + 4) - Real.sqrt ((x + 4) ^ 2 + 1)| := by 
        rw [Real.sqrt_sq_eq_abs]
      linarith
    linarith [abs_nonneg (Real.sqrt ((x + 2) ^ 2 + 4) - Real.sqrt ((x + 4) ^ 2 + 1)), h3]