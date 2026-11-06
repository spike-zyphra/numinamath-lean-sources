import Mathlib

theorem algebra_120333 {a b x y : ℝ} (h1 : x + y = a + b) (h2 : x ^ 2 + y ^ 2 = a ^ 2 + b ^ 2) :
    x ^ 2013 + y ^ 2013 = a ^ 2013 + b ^ 2013 := by 
  have h3 : x * y = a * b := by
    have eq1 : (x + y) ^ 2 = (a + b) ^ 2 := by
      rw [show x + y = a + b by linarith [h1]]
    have eq2 : (x + y) ^ 2 = x^2 + y^2 + 2 * (x * y) := by 
      ring
    have eq3 : (a + b) ^ 2 = a^2 + b^2 + 2 * (a * b) := by 
      ring
    rw [eq2] at eq1
    rw [eq3] at eq1
    have eq4 : x^2 + y^2 = a^2 + b^2 := by 
      linarith [h2]
    linarith [eq1, eq4]
  have h4 : (x - y) ^ 2 = (a - b) ^ 2 := by
    have h5 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by
      ring
    have h6 : (a - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by
      ring
    rw [h5, h6]
    rw [show x + y = a + b by linarith [h1]]
    rw [show x * y = a * b by linarith [h3]]
  have h6 : x - y = a - b ∨ x - y = b - a := by 
    have h7 : (x - y) ^ 2 - (a - b) ^ 2 = 0 := by 
      linarith [h4]
    have h8 : ((x - y) - (a - b)) * ((x - y) + (a - b)) = 0 := by 
      linarith [h7]
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- h9: ((x - y) - (a - b)) = 0
      left
      linarith [h9]
    · -- h10: ((x - y) + (a - b)) = 0
      right
      linarith [h10]
  cases h6 with
  | inl h7 =>
    have hx : x = a := by 
      nlinarith [h7, h1]
    have hy : y = b := by 
      nlinarith [h7, h1, hx]
    rw [hx, hy]
    all_goals ring_nf
  | inr h8 =>
    have hx : x = b := by 
      nlinarith [h8, h1]
    have hy : y = a := by 
      nlinarith [h8, h1, hx]
    rw [hx, hy]
    all_goals ring_nf