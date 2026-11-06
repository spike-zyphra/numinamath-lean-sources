import Mathlib


theorem algebra_174049 {a b c : ℝ} (h₀ : (a + b) * (b + c) * (c + a) = a * b * c)
    (h₁ : (a ^ 3 + b ^ 3) * (b ^ 3 + c ^ 3) * (c ^ 3 + a ^ 3) = a ^ 3 * b ^ 3 * c ^ 3) :
    a * b * c = 0 := by 
  have eq2 : (a ^ 3 + b ^ 3) * (b ^ 3 + c ^ 3) * (c ^ 3 + a ^ 3) = (a + b) * (b + c) * (c + a) * ((a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) * (c ^ 2 - c * a + a ^ 2)) := by
    have h2 : a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2) := by
      ring
    have h3 : b ^ 3 + c ^ 3 = (b + c) * (b ^ 2 - b * c + c ^ 2) := by
      ring
    have h4 : c ^ 3 + a ^ 3 = (c + a) * (c ^ 2 - c * a + a ^ 2) := by
      ring
    rw [h2, h3, h4]
    all_goals ring
  rw [eq2] at h₁
  rw [h₀] at h₁
  by_cases h2 : a * b * c = 0
  · exact h2
  · -- Assume $a \cdot b \cdot c \neq 0$, derive a contradiction.
    have h3 : a * b * c ≠ 0 := by
      intro h
      apply h2
      all_goals linarith
    have eq4 : (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) * (c ^ 2 - c * a + a ^ 2) = a^2 * b^2 * c^2 := by
      apply (mul_left_inj' (show a * b * c ≠ 0 by assumption)).mp
      linarith
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
      sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b))]