import Mathlib

theorem algebra_315049 {a b c : ℝ} (h₀ : a + b + c = 2) (h₁ : a^2 + b^2 + c^2 = 2) :
    a * (1 - a)^2 = b * (1 - b)^2 ∧ b * (1 - b)^2 = c * (1 - c)^2 := by
  have h2 : a * b + b * c + c * a = 1 := by
    have h6 : a * b + b * c + c * a = 1 := by
      have h7 : (a + b + c)^2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by
        ring
      rw [h₀, h₁] at h7
      nlinarith
    linarith
  constructor
  · -- Assume $h₀ : a + b + c = 2$ and $h₁ : a^2 + b^2 + c^2 = 2$, prove $a * (1 - a)^2 = b * (1 - b)^2$
    -- Use nlinarith but avoid intermediate computationally intensive approaches
    have h3 : (a - b) * ( 1 - 2 * (a + b) + (a^2 + a * b + b^2) ) = 0 := by
      have h8 : c = 2 - a - b := by linarith [h₀]
      rw [h8] at h2 h₁
      nlinarith [sq_nonneg (a - b), sq_nonneg (2 - a - b - a), sq_nonneg (2 - a - b - b)]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case where $a - b = 0$
      have hab : a = b := by linarith
      rw [show b = a by linarith [hab]]
      all_goals nlinarith
    · -- Case where $1 - 2*(a + b) + (a^2 + a*b + b^2) = 0$
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1)]
  · -- Assume $h₀ : a + b + c = 2$ and $h₁ : a^2 + b^2 + c^2 = 2$, prove $b * (1 - b)^2 = c * (1 - c)^2$
    have h3 : (b - c) * ( 1 - 2 * (b + c) + (b^2 + b * c + c^2) ) = 0 := by
      have h8 : a = 2 - b - c := by linarith [h₀]
      rw [h8] at h2 h₁
      nlinarith [sq_nonneg (b - c), sq_nonneg (2 - b - c - b), sq_nonneg (2 - b - c - c)]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case where $b - c = 0$
      have hbc : b = c := by linarith
      rw [show c = b by linarith [hbc]]
      all_goals nlinarith
    · -- Case where $1 - 2*(b + c) + (b^2 + b*c + c^2) = 0$
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c - 1)]