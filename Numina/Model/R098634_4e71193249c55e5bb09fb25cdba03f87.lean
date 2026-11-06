import Mathlib

theorem algebra_148603 {a b x : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hroots : x^2 - 4 * a^2 * b^2 * x = 4) (hx1 : x = (a^2 + b^2)^2) :
    a^4 - b^4 = 2 ∨ a^4 - b^4 = -2 := by 
  rw [hx1] at hroots
  have eq1 : (a^2 + b^2) ^ 4 - 4 * a^2 * b^2 * (a^2 + b^2) ^ 2 - 4 = 0 := by
    nlinarith
  have h_eq2 : (a^4 - b^4) ^ 2 - 4 = 0 := by
    nlinarith [sq_nonneg (a^2 * b^2), sq_nonneg (a^2 - b^2), sq_nonneg (a^2 + b^2)]
  have h_eq3 : (a^4 - b^4 - 2) * (a^4 - b^4 + 2) = 0 := by
    nlinarith [h_eq2]
  cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
  · left 
    linarith
  · right 
    linarith