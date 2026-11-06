import Mathlib

open Real

theorem algebra_4893 :
  IsLeast {x : ℝ | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ a > b ∧ x = a + 1 / (b * (a - b))} 3 := by
  constructor
  · -- Show 3 is in the set
    use 2, 1
    norm_num
  · -- Show 3 is the minimum
    intro x h
    rcases h with ⟨a, b, ha, hb, hab, hx⟩
    have h1 : a - b > 0 := by linarith
    have h2 : b * (a - b) > 0 := by
      apply mul_pos
      all_goals linarith
    have h3 : a + 1 / (b * (a - b)) ≥ 3 := by
      have h4 : b * (a - b) > 0 := h2
      have h5 : a + 1 / (b * (a - b)) - 3 ≥ 0 := by
        have h6 : a + 1 / (b * (a - b)) - 3 =
            (a * b * (a - b) + 1 - 3 * b * (a - b)) / (b * (a - b)) := by
          field_simp
          <;> ring
        rw [h6]
        apply div_nonneg
        · -- Show the numerator is non-negative
          nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 1), sq_nonneg (a - b - 1), sq_nonneg (a * b - 1), sq_nonneg (a - 2 * b), sq_nonneg (b * (a - b) - 1), sq_pos_of_pos (show 0 < a - b by linarith), sq_pos_of_pos (show 0 < b by linarith), sq_nonneg (a - 2), sq_nonneg (a - 2 * b), mul_pos (show (0 : ℝ) < a - b by linarith) (show (0 : ℝ) < b by linarith)]
        · -- Show that the denominator is non-negative (it's positive)
          positivity
      linarith
    linarith [hx, h3]