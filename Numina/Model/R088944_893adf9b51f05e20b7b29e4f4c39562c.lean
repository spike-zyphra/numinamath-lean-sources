import Mathlib

theorem inequalities_253590 (x : ℝ) :
    3 * abs (x - 1) + x ^ 2 > 7 ↔ x < -1 ∨ x > 2 := by
  constructor
  · -- Forward: $3|x - 1| + x ^ 2 > 7$ implies $x < -1 ∨ x > 2$
    intro h
    by_cases h1 : x >= 1
    · -- x >=1
      have abs : abs (x - 1) = x - 1 := by
          rw [abs_of_nonneg]
          linarith
      rw [abs] at h
      have h2 : (x - 2) * (x + 5) > 0 := by nlinarith
      cases (mul_pos_iff.mp h2) with
      | inl h6 =>
        right
        nlinarith
      | inr h7 =>
        -- solving second side.
        -- contradiction side need comparing x more than 0
        have h8 : x < -5 := by
          linarith
        nlinarith
    · -- x <1
      have abs : abs (x - 1) = 1 -x := by
        rw [abs_of_neg]
        linarith
        all_goals nlinarith
      rw [abs] at h
      have h3 : (x +1) * (x -4) > 0 := by
        nlinarith
      cases (mul_pos_iff.mp h3) with
      | inl h4 =>
        -- looking solve the right need
        have h5 : x > 4 := by
          nlinarith
        -- contradiction h.
        nlinarith
      | inr h4 =>
        -- solving differently.
        left
        linarith
  · -- Backward h: x < -1 ∨ x > 2
    rintro (h1 | h2)
    · -- x < -1. Forward prove of right side
      have h3 : abs (x - 1) = 1 -x := by
        rw [abs_of_neg]
        linarith
        all_goals nlinarith
      rw [h3]
      nlinarith [sq_nonneg (x + 5), sq_nonneg (x -4)]
    · -- x > 2. Forward prove of right side
      have h4 : abs (x - 1) = x -1 := by
        rw [abs_of_nonneg]
        linarith
      rw [h4]
      nlinarith [sq_nonneg (x + 5), sq_nonneg (x -4)]