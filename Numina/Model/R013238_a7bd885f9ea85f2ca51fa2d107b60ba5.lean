import Mathlib

theorem algebra_299176 (x : ℝ) : (6 * x + 7) ^ 2 * (3 * x + 4) * (x + 1) = 6 ↔
    x = -2 / 3 ∨ x = -5 / 3 := by 
  constructor
  · -- Assume (6 * x + 7) ^ 2 * (3 * x + 4) * (x + 1) = 6, prove x = -2 / 3 ∨ x = -5 / 3 
    intro h
    have h1 : (6 * x + 7) ^ 2 * ((3 * x + 4) * (x + 1)) = 6 := by
      nlinarith
    have eq1 : (6 * x + 7) ^ 2 * ((3 * x + 4) * (x + 1)) = (6 * x + 7) ^ 2 * ( ((6 * x + 7) + 1) / 2 * ((6 * x + 7) - 1) / 6 ) := by 
      have h3 : 3 * x + 4 = ((6 * x + 7) + 1) / 2 := by
        nlinarith
      have h4 : (x + 1) = ((6 * x + 7) - 1) / 6 := by
        nlinarith
      rw [h3, h4]
      <;> ring_nf
    rw [eq1] at h1
    have eq2 : (6 * x + 7) ^ 4 - (6 * x + 7) ^ 2 - 72 = 0 := by 
      nlinarith 
    have eq3 : (6 * x + 7) ^ 2 - 9 = 0 := by
      nlinarith [sq_nonneg ((6 * x + 7) ^ 2 - 9), sq_nonneg (6 * x + 7)]
    have eq4 : (6 * x + 7) ^ 2 = 9 := by
      linarith 
    have eq5 : 6 * x + 7 = 3 ∨ 6 * x + 7 = -3 := by
      have h6 : ((6 * x + 7) - 3) * ((6 * x + 7) + 3) = 0 := by
        nlinarith 
      cases (mul_eq_zero.1 h6) with
      | inl h7 =>
        left
        linarith 
      | inr h8 =>
        right 
        linarith 
    cases eq5 with
    | inl h6 =>
      left
      nlinarith 
    | inr h6 =>
      right 
      nlinarith 
  · -- Assume x = -2 / 3 ∨ x = -5 / 3, prove (6 * x + 7) ^ 2 * (3 * x + 4) * (x + 1) = 6 
    rintro (h | h)
    · -- x = -2 / 3 
      rw [h]
      norm_num 
    · -- x = -5 / 3 
      rw [h]
      norm_num