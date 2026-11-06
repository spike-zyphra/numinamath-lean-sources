import Mathlib

theorem algebra_236272 {x y : ℝ} (h1 : x * y ^ 3 = -135) (h2 : (x + y) * y = -6) :
    (x = -5 ∧ y = 3) ∨ (x = 5 ∧ y = -3) := by

  have eq3 : x * y + y^2 = -6 := by 
    nlinarith

  have eq4 : x * y^3 = (x * y) * y^2 := by 
    ring

  have eq5 : x * y = -6 - y^2 := by
    nlinarith

  rw [eq4] at h1
  rw [eq5] at h1

  have h3 : y^4 + 6 * y^2 - 135 = 0 := by 
    nlinarith [sq_nonneg (y^2), sq_nonneg (y)]

  have h4 : y^2 = 9 := by 
    nlinarith [sq_nonneg (y^2), sq_nonneg (y^2 + 6)]

  have h5 : y = 3 ∨ y = -3 := by
    have h6 : y^2 - 9 = 0 := by nlinarith
    have h7 : (y - 3) * (y + 3) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h7) with h8 h9
    · left 
      linarith 
    · right 
      linarith

  cases h5 with
  | inl hy3 =>
    have hx : x = -5 := by
      rw [hy3] at eq3
      nlinarith 
    left 
    constructor 
    · exact hx
    · exact hy3
  | inr hy3 =>
    have hx : x = 5 := by 
      rw [hy3] at eq3
      nlinarith 
    right 
    constructor 
    · exact hx
    · exact hy3