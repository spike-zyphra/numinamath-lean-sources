import Mathlib

theorem algebra_100889 (a b : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + a * x + b) :
    ∃ x₀ ∈ Set.Icc (-1) 1, |f x₀| + a ≥ 0 := by 
  by_cases ha : a ≥ 0 
  · -- If a ≥ 0, take x₀ = 0 which belongs to [−1,1].
    use 0
    constructor
    · norm_num
    · simp [hf]
      linarith [abs_nonneg (b), ha]
  · -- Now assume a < 0
    by_cases h1 : |f 1| + a ≥ 0
    · -- If |f 1| + a ≥ 0, then take x₀ = 1
      use 1
      constructor
      · norm_num
      · linarith [abs_nonneg (f 1), h1]
    · -- Now assume |f 1| + a < 0
      have h2 : |f 1| < -a := by linarith [abs_nonneg (f 1), show a < 0 by linarith]
      by_cases h3 : |f (-1)| + a ≥ 0
      · -- If |f (-1)| + a ≥ 0, then take x₀ = -1
        use -1
        constructor
        · norm_num
        · linarith [abs_nonneg (f (-1)), h3]
      · -- Assume |f (-1)| + a < 0
        have h4 : |f (-1)| < -a := by linarith [abs_nonneg (f (-1)), show a < 0 by linarith]
        -- Let's compute expressions of f(1) and f(-1)
        have h1a : f 1 = 1 + a + b := by
          rw [hf]
          ring
        have h1b : f (-1) = 1 - a + b := by
          rw [hf]
          ring
        rw [h1a] at h2
        rw [h1b] at h4
        -- Apply triangular inequality on the expressions
        cases' abs_cases (1 + a + b) with h h <;> cases' abs_cases (1 - a + b)  with k k <;> 
          nlinarith