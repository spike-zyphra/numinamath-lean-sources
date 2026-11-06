import Mathlib

theorem number_theory_76279 (n : ℕ) (hn : n > 0) :
    ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ a + b + c + d = n * Real.sqrt (a * b * c * d) ↔
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
  by_cases h1 : n = 1
  · -- Case n = 1
    use 4, 4, 4, 4
    simp [h1]
    <;> ring_nf <;> norm_num
    <;> nlinarith [Real.sqrt_nonneg (4 * 4 * 4 * 4 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (4 * 4 * 4 * 4 : ℝ) by norm_num)]
  · -- n ≠ 1
    by_cases h2 : n = 2
    · -- Case n = 2
      use 2, 2, 2, 2
      simp [h2]
      <;> ring_nf <;> norm_num
      <;> nlinarith [Real.sqrt_nonneg (2 * 2 * 2 * 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * 2 * 2 * 2 : ℝ) by norm_num)]
    · -- n ≠ 2
      by_cases h3 : n = 3
      · -- Case n = 3
        use 1, 2, 2, 1
        simp [h3]
        <;> ring_nf <;> norm_num
        <;> nlinarith [Real.sqrt_nonneg (1 * 2 * 2 * 1 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (1 * 2 * 2 * 1 : ℝ) by norm_num)]
      · -- n ≠ 3
        by_cases h4 : n = 4
        · -- Case n = 4
          use 1, 1, 1, 1
          simp [h4]
          <;> ring_nf <;> norm_num
          <;> nlinarith [Real.sqrt_nonneg (1 * 1 * 1 * 1 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (1 * 1 * 1 * 1 : ℝ) by norm_num)]
        · -- n > 4
          have h5 : n ≥ 5 := by
            omega
          use 0, 0, 0, 0
          simp at *
          <;> omega