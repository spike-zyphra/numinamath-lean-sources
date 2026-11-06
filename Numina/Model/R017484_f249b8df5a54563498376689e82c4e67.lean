import Mathlib

theorem algebra_315731 {a b c : ℝ} (h₁ : abs (a - b) = 1) (h₂ : abs (b + c) = 1)
    (h₃ : abs (a + c) = 2) : abs (a + b + 2 * c) = 3 := by
  cases' eq_or_eq_neg_of_abs_eq h₁ with h1 h1
  · -- Case $a - b = 1$
    cases' eq_or_eq_neg_of_abs_eq h₂ with h2 h2
    · -- Case $b + c = 1$
      cases' eq_or_eq_neg_of_abs_eq h₃ with h3 h3
      · -- Case $a + c = 2$
        have h4 : a + b + 2 * c = 3 := by
          linarith
        rw [h4]
        norm_num
      · -- Case $a + c = -2$
        exfalso
        have h5 : a - b = -3 := by
          linarith
        have h6 : abs (a - b) = 3 := by
          rw [show a - b = -3 by linarith]
          norm_num
        linarith [h₁, h6]
    · -- Case $b + c = -1$
      cases' eq_or_eq_neg_of_abs_eq h₃ with h3 h3
      · -- Case $a + c = 2$
        exfalso
        have h5 : a - b = 3 := by
          linarith
        have h6 : abs (a - b) = 3 := by
          rw [show a - b = 3 by linarith]
          norm_num
        linarith [h₁, h6]
      · -- Case $a + c = -2$
        exfalso
        have h5 : a - b = -1 := by
          linarith
        have h6 : abs (a - b) = 1 := by
          rw [show a - b = -1 by linarith]
          norm_num
        linarith [h₁, h6]
  · -- Case $a - b = -1$
    cases' eq_or_eq_neg_of_abs_eq h₂ with h2 h2
    · -- Case $b + c = 1$
      cases' eq_or_eq_neg_of_abs_eq h₃ with h3 h3
      · -- Case $a + c = 2$
        exfalso
        have h5 : a - b = 1 := by
          linarith
        have h6 : abs (a - b) = 1 := by
          rw [show a - b = 1 by linarith]
          norm_num
        linarith [h₁, h6, h5]
      · --  a + c = -2
        exfalso
        have h5 : a - b = -3 := by
          linarith
        have h6 : abs (a - b) = 3 := by
          rw [show a - b = -3 by linarith]
          norm_num
        linarith [h₁, h6, h5]
    · -- Case $b + c = -1$
      cases' eq_or_eq_neg_of_abs_eq h₃ with h3 h3
      · -- Case $a + c = 2$
        exfalso
        have h5 : a - b = 3 := by
          linarith
        have h6 : abs (a - b) = 3 := by
          rw [show a - b = 3 by linarith]
          norm_num
        linarith [h₁, h6, h5]
      · -- Case $a + c = -2$
        have h4 : a + b + 2 * c = -3 := by
          linarith
        rw [h4]
        norm_num