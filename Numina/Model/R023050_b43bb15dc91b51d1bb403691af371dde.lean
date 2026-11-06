import Mathlib

theorem algebra_5087
    {a b : ℝ}
    (ha : a ≠ 0)
    (hb : b ≠ 0)
    (h : a * b = a - b) :
    a / b + b / a - a * b = 2 := by

  have eq1 : a / b + b / a = (a^2 + b^2) / (a * b) := by 
    field_simp
    <;> ring

  have eq3 : a / b + b / a - a * b = ( (a^2 + b^2) / (a * b) - (a * b) ) := by
    rw [eq1]
    all_goals ring

  have eq4 : ( (a^2 + b^2) / (a * b) - (a * b) ) = 2 := by
    have h1 : a - b ≠ 0 := by
      by_contra h1
      have eq14 : a = b := by linarith
      have h2 : a * b = a - b := h
      rw [show b = a by nlinarith [eq14] ] at h2
      have eq16 : a ^ 2 = 0 := by 
        nlinarith [sq_pos_of_ne_zero (show (a) ≠ 0 by exact ha), sq_pos_of_ne_zero (show (b) ≠ 0 by exact hb)]
      have eq17 : a = 0 := by 
        nlinarith 
      contradiction

    have h1' : a * b ≠ 0 := by
      apply mul_ne_zero
      exact ha
      exact hb

    have eq18 : (a ^ 2 + b ^ 2) - (a * b) * (a * b) = 2 * (a * b) := by
      have h2 : a * b = a - b := h
      have eq10 : a ^ 2 + b ^ 2 = (a - b) ^ 2 + 2 * (a - b) := by 
        have h11 : a * b = a - b := h
        nlinarith [sq_pos_of_ne_zero (show (a) ≠ 0 by exact ha), sq_pos_of_ne_zero (show (b) ≠ 0 by exact hb), sq_nonneg (a - b), sq_nonneg (a * b - (a - b))]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - (a - b)), sq_pos_of_ne_zero h1', sq_pos_of_ne_zero (show (a - b) ≠ 0 by exact h1)]

    field_simp at eq18 ⊢
    <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - (a - b)), sq_pos_of_ne_zero (show (a * b) ≠ 0 by exact h1'), sq_pos_of_ne_zero (show (a - b) ≠ 0 by exact h1)]

  rw [eq3, eq4]
  all_goals linarith