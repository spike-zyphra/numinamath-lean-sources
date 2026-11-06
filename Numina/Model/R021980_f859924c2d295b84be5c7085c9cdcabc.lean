import Mathlib

open Real Set

theorem algebra_100673 : IsGreatest {y : ℝ | ∃ x, y = |sqrt (x^2 + 4 * x + 8) - sqrt (x^2 + 8 * x + 17)|} (sqrt 5) := by
  constructor
  · -- Show that sqrt(5) is in the set. Let's take x = -6
    use -6
    have h1 : sqrt ((-6 : ℝ) ^2 + 4 * (-6) + 8) = Real.sqrt 20 := by
      norm_num
    have h2 : sqrt ((-6 : ℝ) ^2 + 8 * (-6) + 17) = Real.sqrt 5 := by
      norm_num
    have h3 : Real.sqrt (20 : ℝ) = 2 * Real.sqrt 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    have h4 : sqrt ((-6 : ℝ) ^2 + 4 * (-6) + 8) = 2 * Real.sqrt 5 := by
      rw [h1, h3]
    have h5 : sqrt ((-6 : ℝ) ^2 + 8 * (-6) + 17) = Real.sqrt 5 := h2
    have eq1 : |(2 * Real.sqrt 5 : ℝ) - Real.sqrt 5| = Real.sqrt 5 := by
      have h7 : (2 * Real.sqrt 5 : ℝ) - Real.sqrt 5 = Real.sqrt 5 := by
        ring
      rw [h7]
      all_goals
        have h8 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
        have h9 : |Real.sqrt 5| = Real.sqrt 5 := abs_of_nonneg h8
        simpa using h9
    rw [h4, h5]
    rw [eq1]
    all_goals norm_num
  · -- Show that sqrt(5) is greatest
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h5 : (x ^ 2 + 4 * x + 8) ≥ 0 := by
      nlinarith [sq_nonneg (x + 2)]
    have h6 : (x ^ 2 + 8 * x + 17) ≥ 0 := by
      nlinarith [sq_nonneg (x + 4)]
    have h1 : sqrt (x ^ 2 + 4 * x + 8) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 4 * x + 8)
    have h2 : sqrt (x ^ 2 + 8 * x + 17) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 8 * x + 17)
    have h3 : (sqrt (x ^ 2 + 4 * x + 8) - sqrt (x ^ 2 + 8 * x + 17)) ^ 2 ≤ (5 : ℝ) := by
      nlinarith [sq_nonneg (sqrt (x ^ 2 + 4 * x + 8) - sqrt (x ^ 2 + 8 * x + 17) - Real.sqrt 5), sq_nonneg (sqrt (x ^ 2 + 4 * x + 8) - (sqrt (x ^ 2 + 8 * x + 17) + Real.sqrt 5)), 
          sq_nonneg (x + 6), 
          Real.sqrt_nonneg (5 : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
          Real.sqrt_nonneg (x ^ 2 + 4 * x + 8), 
          Real.sqrt_nonneg (x ^ 2 + 8 * x + 17), 
          mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 4 * x + 8)) (Real.sqrt_nonneg (x ^ 2 + 8 * x + 17)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 2 + 4 * x + 8 : ℝ) by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 2 + 8 * x + 17 : ℝ) by nlinarith), 
          sq_nonneg (x + 10 / 3), 
          sq_nonneg (x + 6)
          ]
    have h4 : |sqrt (x ^ 2 + 4 * x + 8) - sqrt (x ^ 2 + 8 * x + 17)| ≤ Real.sqrt 5 := by
      have h5 : (sqrt (x ^ 2 + 4 * x + 8) - sqrt (x ^ 2 + 8 * x + 17)) ^ 2 ≤ (5 : ℝ) := h3
      have h8 : Real.sqrt ((sqrt (x ^ 2 + 4 * x + 8) - sqrt (x ^ 2 + 8 * x + 17)) ^ 2) ≤ Real.sqrt (5 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h9 : Real.sqrt ((sqrt (x ^ 2 + 4 * x + 8) - sqrt (x ^ 2 + 8 * x + 17)) ^ 2) = |sqrt (x ^ 2 + 4 * x + 8) - sqrt (x ^ 2 + 8 * x + 17)| := by
        rw [Real.sqrt_sq_eq_abs]
      linarith [h8, h9]
    linarith [h4, hx]