import Mathlib

theorem algebra_26 {n : ℝ} (hn : n ≥ 2) (x : ℝ) :
    2 * x + (n ^ 2 + n - 2) / (2 * x + 1) = 2 * n ↔
    x = (n - 2) / 2 ∨ x = (n + 1) / 2 := by
  constructor
  · -- Assume 2 * x + (n ^ 2 + n - 2) / (2 * x + 1) = 2 * n, prove x = (n - 2) / 2 ∨ x = (n + 1) / 2
    intro h
    have h1 : 2 * x + 1 ≠ 0 := by
      by_contra h1
      have h1_eq : x = -1 / 2 := by linarith
      rw [h1_eq] at h
      norm_num [h1_eq] at h
      all_goals nlinarith

    have h2 : 2 * x + (n ^ 2 + n - 2) / (2 * x + 1) = 2 * n := h

    -- Multiply both sides by $2 * x + 1$ to clear the denominator
    have h3 : (2 * x + (n ^ 2 + n - 2) / (2 * x + 1) ) * (2 * x + 1) = (2 * n) * (2 * x + 1) := by
      rw [h2]

    have h4 : (2 * x + (n ^ 2 + n - 2) / (2 * x + 1) ) * (2 * x + 1) = (2 * x) * (2 * x + 1) + (n ^ 2 + n - 2) := by
      field_simp [h1]
      <;> ring

    have h4_eq : (2 * x) * (2 * x + 1) + (n ^ 2 + n - 2) = (2 * n) * (2 * x + 1) := by
      rw [h4] at h3
      linarith

    -- Form a quadratic equation
    have h5 : 4 * x ^ 2 + (2 - 4 * n) * x + (n ^ 2 - n - 2) = 0 := by
      linarith [h4_eq]

    -- Solve the quadratic
    have h6 : (x - (n - 2) / 2) * (x - (n + 1) / 2) = 0 := by
      nlinarith [sq_nonneg (x - (n - 2) / 2), sq_nonneg (x - (n + 1) / 2), h5 ]

    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case 1: x - (n - 2) / 2 = 0
      left
      linarith

    · -- Case 2: x - (n + 1) / 2 = 0
      right
      linarith
  · -- Assume x = (n - 2) / 2 ∨ x = (n + 1) / 2 prove 2 * x + (n ^ 2 + n - 2) / (2 * x + 1) = 2 * n
    rintro (h | h)
    · -- Case 1: x = (n - 2) / 2
      have h_eq : x = (n - 2) / 2 := h
      have h1 : 2 * x + 1 = n - 1 := by
        linarith [h_eq]

      have h3 : (2 * x + 1) ≠ 0 := by
        rw [show 2 * x + 1 = n - 1 by linarith [h_eq] ]
        nlinarith [show n ≥ 2 by linarith]

      -- Rewrite the equation
      have h4 : 2 * x + (n ^ 2 + n - 2) / (2 * x + 1) = 2 * n := by
        rw [show 2 * x + 1 = n - 1 by linarith [h_eq]]
        have h7 : n - 1 ≠ 0 := by
          nlinarith [show n ≥ 2 by linarith]
        field_simp [h7]
        <;> nlinarith [sq_nonneg (n - 1)]
      exact h4

    · -- Case 2: x = (n + 1) / 2
      have h_eq : x = (n + 1) / 2 := h
      have h1 : 2 * x + 1 = n + 2 := by
        linarith [h_eq]

      have h3 : (2 * x + 1) ≠ 0 := by
        rw [show 2 * x + 1 = n + 2 by linarith [h_eq] ]
        nlinarith [show n ≥ 2 by linarith]

      -- Rewrite the equation
      have h4 : 2 * x + (n ^ 2 + n - 2) / (2 * x + 1) = 2 * n := by
        rw [show 2 * x + 1 = n + 2 by linarith [h_eq]]
        have h7 : n + 2 ≠ 0 := by
          nlinarith [show n ≥ 2 by linarith]
        field_simp [h7]
        <;> nlinarith [sq_nonneg (n + 2)]
      exact h4