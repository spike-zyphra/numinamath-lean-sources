import Mathlib

/- Given the inequality in terms of $x$, $x^2 - (m+2)x > 0$, has the solution set $\{x|x < 0 \text{ or } x > 2\}$, find the value of $m$. -/
theorem algebra_9423 {m : ℝ} (h : ∀ x, x^2 - (m + 2)*x > 0 ↔ x < 0 ∨ x > 2) :
    m = 0 := by

  -- Solve the inequality x^2 - (m + 2)x > 0
  -- x > 0 and x > m + 2 or x < 0 and x < m + 2
  conv at h =>
    intro x
    lhs
    rw [(by ring : x^2 - (m + 2)*x = x * (x - m - 2)), gt_iff_lt, mul_pos_iff]

  -- Cases : m ≤ -2 ∨ m > -2
  obtain k | k := le_or_gt m (-2)

  . -- Case 1: m ≤ -2
    -- Plug in x = 1
    specialize h 1
    simp [(by norm_num : ¬ (1 : ℝ) < 0)] at h
    -- We get 1 ≤ 2 + m, contradiction
    linarith

  . -- Case 2: m > -2
    -- Prove by contradiction
    -- Suppose m ≠ 0
    by_contra! h1
    -- Cases : m < 0 ∨ m > 0
    obtain h1 | h1 := lt_or_gt_of_ne h1

    . -- Case 1: m < 0
      -- Set x = 2 + m / 2
      specialize h (2 + m / 2)
      simp at h
      have h2 : ¬ 2 + m / 2 < 0 := by linarith
      have h3 : ¬ 0 < m := by linarith
      have h4 : 2 + m / 2 > 0 := by linarith
      simp [h2, h3, h4] at h
      -- Simplify at h and we get 0 ≤ m, contradiction
      linarith

    . -- Case 2: m > 0
      -- Set x = 2 + m / 2
      specialize h (2 + m / 2)
      simp at h
      have h2 : ¬ 2 + m / 2 < 0 := by linarith
      have h3 : 2 + m / 2 > 0 := by linarith
      -- Simplify at h and we get 0 ≤ m, contradiction
      simp [h1, h2, h3] at h
      linarith
