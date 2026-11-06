import Mathlib

theorem algebra_262830 (a b c : ℝ) (h₀ : a * b * c = 1) (h₁ : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b ≤ 1 ∧ c ≤ 1) ∨ (b > 1 ∧ a ≤ 1 ∧ c ≤ 1) ∨ (c > 1 ∧ a ≤ 1 ∧ b ≤ 1) := by
  have h2 : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 := by
    constructor
    · -- Assume a = 0, then a * b * c = 0 ≠ 1.
      by_contra h
      have h3 : a * b * c = 0 := by
        rw [h]
        norm_num
      linarith
    constructor
    · -- Assume b = 0, then a * b * c = 0 ≠ 1.
      by_contra h
      have h3 : a * b * c = 0 := by
        rw [h]
        norm_num
      linarith
    · -- Assume c = 0, then a * b * c = 0 ≠ 1.
      by_contra h
      have h3 : a * b * c = 0 := by
        rw [h]
        norm_num
      linarith
  have h3 : 1 / a = b * c := by
    have h4 : a ≠ 0 := h2.1
    have h5 : b ≠ 0 := h2.2.1
    have h6 : c ≠ 0 := h2.2.2
    field_simp [h4, h5, h6]
    nlinarith [h₀]
  have h4 : 1 / b = a * c := by
    have h4 : a ≠ 0 := h2.1
    have h5 : b ≠ 0 := h2.2.1
    have h6 : c ≠ 0 := h2.2.2
    field_simp [h4, h5, h6]
    nlinarith [h₀]
  have h5 : 1 / c = a * b := by
    have h4 : a ≠ 0 := h2.1
    have h5 : b ≠ 0 := h2.2.1
    have h6 : c ≠ 0 := h2.2.2
    field_simp [h4, h5, h6]
    nlinarith [h₀]
  have h6 : a + b + c > b * c + a * c + a * b := by
    have h4' : 1 / a + 1 / b + 1 / c = b * c + a * c + a * b := by
      rw [h3, h4, h5]
      all_goals nlinarith
    linarith [h₁, h4']
  -- Now, we need to prove that exactly one of them is greater than 1.
  -- We will prove that if two of them are greater than 1, then the given condition is false.
  by_cases ha1 : a > 1
  · -- Assume a > 1, we need to show b ≤ 1 and c ≤ 1
    by_cases hb1 : b > 1
    · -- Assume a > 1 and b > 1.
      -- From h₀ : a * b * c = 1, with a > 1, b > 1:
      -- Then $c = \frac{1}{a \cdot b} < 1$.
      have hc1 : c < 1 := by
        have : a * b > 1 := by nlinarith
        nlinarith [h₀, mul_pos (show 0 < a - 1 by linarith) (show 0 < b - 1 by linarith)]
      exfalso
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos (show 0 < a - 1 by linarith) (show 0 < b - 1 by linarith),
        mul_pos (show 0 < b - 1 by linarith) (show 0 < 1 - c by linarith),
        mul_pos (show 0 < a - 1 by linarith) (show 0 < 1 - c by linarith),
        h₀, h6]
    · -- Assume a > 1 and b ≤ 1.
      by_cases hc1 : c > 1
      · -- Assume a > 1, b ≤ 1 and c > 1.
        exfalso
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos (show 0 < a - 1 by linarith) (show 0 < c - 1 by linarith),
          mul_nonneg (show 0 ≤ 1 - b by linarith) (show 0 ≤ c - 1 by linarith),
          mul_nonneg (show 0 ≤ 1 - b by linarith) (show 0 ≤ a - 1 by linarith),
          h₀, h6]
      · -- Assume a > 1, b ≤ 1 and c ≤ 1. This matches the first part of the goal.
        left
        constructor
        · linarith
        constructor
        · nlinarith
        · nlinarith
  · -- Assume that a ≤ 1.
    by_cases hb1 : b > 1
    · -- Assume a ≤ 1 and b > 1.
      by_cases hc1 : c > 1
      · -- Assume a ≤ 1, b > 1 and c > 1.
        exfalso
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos (show 0 < b - 1 by linarith) (show 0 < c - 1 by linarith),
          mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ c - 1 by linarith),
          mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ b - 1 by linarith),
          h₀, h6]
      · -- Assume a ≤ 1, b > 1 and c ≤ 1. This matches the second part of the goal.
        right
        left
        constructor
        · linarith
        constructor
        · nlinarith
        · nlinarith
    · -- Assume a ≤ 1 and b ≤ 1.
      by_cases hc1 : c > 1
      · -- Assume a ≤ 1, b ≤ 1 and c > 1. This matches the third part of the goal.
        right
        right
        constructor
        · linarith
        constructor
        · nlinarith
        · nlinarith
      · -- Assume a ≤ 1, b ≤ 1 and c ≤ 1. This is the trivial case.
        -- Goal: Show the original goal holds.
        -- This means none of the variables is greater than 1.
        -- But this is impossible because the sum is greater than the product sum.
        -- Actually, this case is impossible from h6.
        -- Let's check - this case should be impossible.
        -- If a ≤ 1, b ≤ 1, c ≤ 1, then we must have a = b = c = 1.
        -- Now, given the condition $a + b + c > \sum_{\text{cyc}} ab$, with $a \cdot b \cdot c = 1$
        -- But if $a \leq 1, b \leq 1, c \leq 1$ and $a \cdot b \cdot c = 1$, then $a = b = c = 1$.
        -- But then $a + b + c = 3$ and $\sum ab = 3$, so $3 > 3$ is false.
        -- So our hypothesis is a contradiction.
        exfalso
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          h₀, h6, mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 - b by linarith),
          mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 - c by linarith),
          mul_nonneg (show 0 ≤ 1 - b by linarith) (show 0 ≤ 1 - c by linarith)]