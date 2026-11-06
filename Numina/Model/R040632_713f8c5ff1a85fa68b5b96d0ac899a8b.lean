import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_96223 {a b : ℝ} (ha : 1 < b) (hb : b ≤ a) :
    logb a (a / b) + logb b (b / a) ≤ 0 := by
  have h1 : 1 < a := by
    linarith
  have h2 : logb a (a / b) = logb a a - logb a b := by
    rw [logb_div (by linarith) (by linarith)]
  have h3 : logb a a = 1 := by
    rw [logb_self_eq_one]
    all_goals linarith
  have h4 : logb b (b / a) = logb b b - logb b a := by
    rw [logb_div (by linarith) (by linarith)]
  have h5 : logb b b = 1 := by
    rw [logb_self_eq_one]
    all_goals linarith
  have h7 : logb a (a / b) + logb b (b / a) = 2 - (logb a b + logb b a) := by
    rw [h2, h3, h4, h5]
    all_goals linarith
  have h8 : logb a b = (log b) / (log a) := by
    field_simp [logb]
  have h9 : logb b a = (log a) / (log b) := by
    field_simp [logb]
  have h10 : log b > 0 := by
    apply log_pos
    all_goals linarith
  have h11 : log a > 0 := by
    apply log_pos
    all_goals linarith
  have h12 : logb a b + logb b a ≥ 2 := by
    rw [h8, h9]
    have h14 : log a * log b > 0 := by
      positivity
    have h15 : (log b / log a + log a / log b) ≥ 2 := by
      have h16 : (log b / log a + log a / log b) - 2 ≥ 0 := by
        have h17 : (log b / log a + log a / log b - 2) = ((log b) ^ 2 + (log a) ^ 2 - 2 * (log a * (log b))) / (log a * log b) := by
          field_simp
          <;> ring
        rw [h17] at *
        apply div_nonneg
        · -- Show that the numerator is non-negative
          nlinarith [sq_nonneg (log b - log a)]
        all_goals -- Show that the denominator is positive
          positivity
      linarith
    linarith
  linarith [h7, h12]