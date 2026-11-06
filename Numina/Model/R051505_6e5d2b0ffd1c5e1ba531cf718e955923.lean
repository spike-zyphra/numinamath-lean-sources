import Mathlib

theorem inequalities_302128 (a b c : ℝ) (h : 12 * a^2 + 7 * b^2 + 5 * c^2 ≤ 12 * a * abs b - 4 * b * abs c - 16 * c - 16) :
    a = 1 / 2 ∧ b = -1 ∧ c = -2 := by
  have h1 : b ≥ 0 ∨ b < 0 := by
    by_cases h2 : b ≥ 0
    · left
      exact h2
    · right
      linarith
  have h2 : c ≥ 0 ∨ c < 0 := by
    by_cases h3 : c ≥ 0
    · left
      exact h3
    · right
      linarith

  cases h1 with
  | inl h1 =>
    cases h2 with
    | inl h2 =>
      rw [abs_of_nonneg h1, abs_of_nonneg h2] at h
      have h3 : (a - b / 2) ^ 2 + (b + c / 2) ^ 2 + (c + 2) ^ 2 ≤ 0 := by
        nlinarith
      have ha1 : a - b / 2 = 0 := by nlinarith [sq_nonneg (a - b / 2), sq_nonneg (b + c / 2), sq_nonneg (c + 2)]
      have hb1 : b + c / 2 = 0 := by nlinarith [sq_nonneg (a - b / 2), sq_nonneg (b + c / 2), sq_nonneg (c + 2)]
      have hc1 : c + 2 = 0 := by nlinarith [sq_nonneg (a - b / 2), sq_nonneg (b + c / 2), sq_nonneg (c + 2)]
      nlinarith
    | inr h2 =>
      rw [abs_of_nonneg h1, abs_of_neg h2] at h
      have h3 : (a - b / 2) ^ 2 + (b - c / 2) ^ 2 + (c + 2) ^ 2 ≤ 0 := by
        nlinarith
      have ha1 : a - b / 2 = 0 := by nlinarith [sq_nonneg (a - b / 2), sq_nonneg (b - c / 2), sq_nonneg (c + 2)]
      have hb1 : b - c / 2 = 0 := by nlinarith [sq_nonneg (a - b / 2), sq_nonneg (b - c / 2), sq_nonneg (c + 2)]
      have hc1 : c + 2 = 0 := by nlinarith [sq_nonneg (a - b / 2), sq_nonneg (b - c / 2), sq_nonneg (c + 2)]
      nlinarith
  | inr h1 =>
    cases h2 with
    | inl h2 =>
      rw [abs_of_neg h1, abs_of_nonneg h2] at h
      have h3 : (a + b / 2) ^ 2 + (b + c / 2) ^ 2 + (c + 2) ^ 2 ≤ 0 := by
        nlinarith
      have ha1 : a + b / 2 = 0 := by nlinarith [sq_nonneg (a + b / 2), sq_nonneg (b + c / 2), sq_nonneg (c + 2)]
      have hb1 : b + c / 2 = 0 := by nlinarith [sq_nonneg (a + b / 2), sq_nonneg (b + c / 2), sq_nonneg (c + 2)]
      have hc1 : c + 2 = 0 := by nlinarith [sq_nonneg (a + b / 2), sq_nonneg (b + c / 2), sq_nonneg (c + 2)]
      nlinarith
    | inr h2 =>
      rw [abs_of_neg h1, abs_of_neg h2] at h
      have h3 : (a + b / 2) ^ 2 + (b - c / 2) ^ 2 + (c + 2) ^ 2 ≤ 0 := by
        nlinarith
      have ha1 : a + b / 2 = 0 := by nlinarith [sq_nonneg (a + b / 2), sq_nonneg (b - c / 2), sq_nonneg (c + 2)]
      have hb1 : b - c / 2 = 0 := by nlinarith [sq_nonneg (a + b / 2), sq_nonneg (b - c / 2), sq_nonneg (c + 2)]
      have hc1 : c + 2 = 0 := by nlinarith [sq_nonneg (a + b / 2), sq_nonneg (b - c / 2), sq_nonneg (c + 2)]
      have ha : a = 1 / 2 := by
        nlinarith
      have hb : b = -1 := by
        nlinarith
      have hc : c = -2 := by
        nlinarith
      exact ⟨ha, hb, hc⟩