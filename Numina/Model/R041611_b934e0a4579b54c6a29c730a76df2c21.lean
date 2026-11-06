import Mathlib

/- The minimum value of $\left| x-1 \right|+8\left| x-2 \right|+a\left| x-3 \right|+2\left| x-4 \right|$ is $12$, then the range of values for $a$ is ___          ___. -/
theorem algebra_7283 (a : ℝ) :
    IsLeast {n | ∃ x, n = abs (x - 1) + 8 * abs (x - 2) + a * abs (x - 3) + 2 * abs (x - 4)} 12 ↔
    a ≥ 7 := by 
  constructor
  · -- Assume $12$ is the minimum value, then $a \geq 7$.
    intro h
    have h1 : 12 ∈ {n | ∃ x, n = abs (x - 1) + 8 * abs (x - 2) + a * abs (x - 3) + 2 * abs (x - 4)} := by
      exact h.left
    have h2 : ∀ n, n ∈ {n | ∃ x, n = abs (x - 1) + 8 * abs (x - 2) + a * abs (x - 3) + 2 * abs (x - 4)} → 12 ≤ n := by
      apply h.right
    -- Check at x = 2 to derive the constraint $a \geq 7$.
    have h5 : (abs ((2 : ℝ) - 1) + 8 * abs ((2 : ℝ) - 2) + a * abs ((2 : ℝ) - 3) + 2 * abs ((2 : ℝ) - 4)) ≥ 12 := by
      have h6 : (abs ((2 : ℝ) - 1) + 8 * abs ((2 : ℝ) - 2) + a * abs ((2 : ℝ) - 3) + 2 * abs ((2 : ℝ) - 4)) ∈ {n | ∃ x, n = abs (x - 1) + 8 * abs (x - 2) + a * abs (x - 3) + 2 * abs (x - 4)} := by
        use (2 : ℝ)
        all_goals linarith
      have h7 := h2 (abs ((2 : ℝ) - 1) + 8 * abs ((2 : ℝ) - 2) + a * abs ((2 : ℝ) - 3) + 2 * abs ((2 : ℝ) - 4)) h6
      linarith
    norm_num [abs] at h5 ⊢
    linarith
  · -- Assume $a \geq 7$, then $12$ is the minimum value.
    intro ha
    constructor
    · -- Show that $12$ is indeed achievable, at $x = 3$.
      use (3 : ℝ)
      norm_num [abs]
      all_goals linarith
    · -- Show that $12$ is minimal.
      intro n hn
      rcases hn with ⟨x, hx⟩
      have h1 : abs (x - 1) + 8 * abs (x - 2) + a * abs (x - 3) + 2 * abs (x - 4) ≥ 12 := by
        by_cases h2 : x ≥ (4 : ℝ)
        · -- x ≥ 4
          rw [abs_of_nonneg (show x - 1 ≥ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonneg (show x - 3 ≥ 0 by linarith), abs_of_nonneg (show x - 4 ≥ 0 by linarith)]
          nlinarith [abs_nonneg (x - 1), abs_nonneg (x - 2), abs_nonneg (x - 3), abs_nonneg (x - 4), show a ≥ 0 by linarith]
        by_cases h3 : x ≥ (3 : ℝ)
        · -- 3 ≤ x < 4
          rw [abs_of_nonneg (show x - 1 ≥ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonneg (show x - 3 ≥ 0 by linarith), abs_of_nonpos (show x - 4 ≤ 0 by linarith)]
          nlinarith [abs_nonneg (x - 1), abs_nonneg (x - 2), abs_nonneg (x - 3), abs_nonneg (x - 4), show a ≥ 0 by linarith]
        by_cases h4 : x ≥ (2 : ℝ)
        · -- 2 ≤ x < 3
          rw [abs_of_nonneg (show x - 1 ≥ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonpos (show x - 3 ≤ 0 by linarith), abs_of_nonpos (show x - 4 ≤ 0 by linarith)]
          nlinarith [abs_nonneg (x - 1), abs_nonneg (x - 2), abs_nonneg (x - 3), abs_nonneg (x - 4), show a ≥ 0 by linarith]
        by_cases h5 : x ≥ (1 : ℝ)
        · -- 1 ≤ x < 2
          rw [abs_of_nonneg (show x - 1 ≥ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith), abs_of_nonpos (show x - 3 ≤ 0 by linarith), abs_of_nonpos (show x - 4 ≤ 0 by linarith)]
          nlinarith [abs_nonneg (x - 1), abs_nonneg (x - 2), abs_nonneg (x - 3), abs_nonneg (x - 4), show a ≥ 0 by linarith]
        · -- x < 1
          rw [abs_of_nonpos (show x - 1 ≤ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith), abs_of_nonpos (show x - 3 ≤ 0 by linarith), abs_of_nonpos (show x - 4 ≤ 0 by linarith)]
          nlinarith [abs_nonneg (x - 1), abs_nonneg (x - 2), abs_nonneg (x - 3), abs_nonneg (x - 4), show a ≥ 0 by linarith]
      linarith