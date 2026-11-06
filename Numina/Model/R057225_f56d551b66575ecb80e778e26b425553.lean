import Mathlib

theorem algebra_244855 {x y : ℝ} (h1 : x^2 - x * y + y^2 = 7) (h2 : x^4 + x^2 * y^2 + y^4 = 91) :
    (x, y) = (-3, -1) ∨ (x, y) = (-1, -3) ∨ (x, y) = (1, 3) ∨ (x, y) = (3, 1) := by

  have h3 : x * y = 3 := by 
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x * y - 3), sq_nonneg (x + y), sq_nonneg (x - y)]

  have h4 : x^2 + y^2 = 10 := by 
    nlinarith [h1, h3]

  have h5 : (x + y)^2 = 16 := by 
    nlinarith [h4, h3]

  have h6 : x + y = 4 ∨ x + y = -4 := by 
    have h7 : (x + y) ^ 2 - 16 = 0 := by linarith
    have h8 : ((x + y) - 4) * ((x + y) + 4) = 0 := by 
      nlinarith 
    cases (mul_eq_zero.mp h8) with 
    | inl h9 =>
      left 
      linarith 
    | inr h10 =>
      right 
      linarith 

  cases h6 with 
  | inl h7 =>
    have h8 : x + y = 4 := h7 
    have h10 : (x - 1) * (x - 3) = 0 := by 
      nlinarith [h8, h3]
    cases (mul_eq_zero.mp h10) with 
    | inl h11 =>
      have hx1 : x = 1 := by linarith 
      have hy1 : y = 3 := by linarith [h8, hx1]
      have h12 : (x, y) = (1, 3) := by 
        exact Prod.ext hx1 hy1
      tauto
    | inr h12 =>
      have hx2 : x = 3 := by linarith 
      have hy2 : y = 1 := by linarith [h8, hx2]
      have h13 : (x, y) = (3, 1) := by 
        exact Prod.ext hx2 hy2
      tauto
  | inr h7 =>
    have h8 : x + y = -4 := h7 
    have h10 : (x + 1) * (x + 3) = 0 := by 
      nlinarith [h8, h3]
    cases (mul_eq_zero.mp h10) with 
    | inl h11 =>
      have hx1 : x = -1 := by linarith 
      have hy1 : y = -3 := by linarith [h8, hx1]
      have h12 : (x, y) = (-1, -3) := by 
        exact Prod.ext hx1 hy1
      tauto
    | inr h12 =>
      have hx2 : x = -3 := by linarith 
      have hy2 : y = -1 := by linarith [h8, hx2]
      have h13 : (x, y) = (-3, -1) := by 
        exact Prod.ext hx2 hy2
      tauto