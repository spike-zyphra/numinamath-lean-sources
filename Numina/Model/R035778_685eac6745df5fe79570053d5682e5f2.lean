import Mathlib

theorem inequalities_197404 (a b c d : ℝ) (ha : 0 < a) (habc : a ≤ b ∧ b ≤ c ∧ c ≤ d) :
    a / b + b / c + c / d + d / a ≥ b / a + c / b + d / c + a / d := by
  rcases habc with ⟨hab, hbc, hcd⟩
  have hb : 0 < b := by linarith
  have hc : 0 < c := by linarith
  have hd : 0 < d := by linarith
  have h1 : 0 < a * b * c * d := by
    positivity
  have h2 : a / b + b / c + c / d + d / a - (b / a + c / b + d / c + a / d) ≥ 0 := by
    have pos1 : 0 < a * b * c * d := h1
    have eq1 : a / b + b / c + c / d + d / a - (b / a + c / b + d / c + a / d) =
        (a^2 * c * d + a * b^2 * d + a * b * c^2 + b * c * d^2 - b^2 * c * d - a * c^2 * d - a * b * d^2 - a^2 * b * c) / (a * b * c * d) := by
      field_simp
      ring
    rw [eq1] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (a - d)),
      sq_nonneg (b * (b - c)), sq_nonneg (b * (b - d)), sq_nonneg (c * (c - d)),
      mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b - a by linarith),
      mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c - a by linarith),
      mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ d - a by linarith),
      mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - b by linarith),
      mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ d - c by linarith),
      mul_nonneg (show 0 ≤ c - b by linarith) (show 0 ≤ d - c by linarith),
      mul_pos ha (show 0 < b by linarith),
      mul_pos ha (show 0 < c by linarith),
      mul_pos ha (show 0 < d by linarith),
      mul_pos (show 0 < b by linarith) (show 0 < c by linarith),
      mul_pos (show 0 < b by linarith) (show 0 < d by linarith),
      mul_pos (show 0 < c by linarith) (show 0 < d by linarith)]
    all_goals positivity
  linarith