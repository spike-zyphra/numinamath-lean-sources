import Mathlib

theorem algebra_297904 (x : ℝ) :
    abs (abs (x - 3) + 3 * x) = 1 ↔ x = -2 ∨ x = -1 := by
  constructor
  · -- First implication: if abs (abs (x - 3) + 3 * x) = 1, prove x = -2 ∨ x = -1
    intro h
    cases eq_or_eq_neg_of_abs_eq h with
    | inl h1 =>
      by_cases h2 : x - 3 ≥ 0
      · -- If $x - 3 \geq 0$, then $|x - 3|= x - 3$
        have h3 : abs (x - 3) = x - 3 := by
          rw [abs_of_nonneg h2]
        rw [h3] at h1
        linarith
      · -- If $x - 3 < 0$, then $|x - 3|= 3 - x$
        have h3 : abs (x - 3) = 3 - x := by
          rw [abs_of_nonpos (show x - 3 ≤ 0 by linarith)]
          all_goals
            linarith
        rw [h3] at h1
        right
        linarith
    | inr h2 =>
      by_cases h3 : x - 3 ≥ 0
      · -- If $x - 3 \geq 0$, then $|x - 3|= x - 3$
        have h4 : abs (x - 3) = x - 3 := by
          rw [abs_of_nonneg h3]
        rw [h4] at h2
        linarith
      · -- If $x - 3 < 0$, then $|x - 3|= 3 - x$
        have h4 : abs (x - 3) = 3 - x := by
          rw [abs_of_nonpos (show x - 3 ≤ 0 by linarith)]
          all_goals
            linarith
        rw [h4] at h2
        left
        linarith
  · -- Second implication: if x = -2 ∨ x = -1, prove abs (abs (x - 3) + 3 * x) = 1
    rintro (h | h)
    · -- Case x = -2
      rw [h]
      norm_num [abs_of_nonpos]
    · -- Case x = -1
      rw [h]
      norm_num [abs_of_nonpos]