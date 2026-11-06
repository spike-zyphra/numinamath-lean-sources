import Mathlib

theorem algebra_3524 (a : ℝ) (ha : 0 < a ∧ a ≠ 3) :
    (3 * 3 * 3 + a * a * a) > (3 * 3 * a + a * a * 3) := by
  have h1 : a > 0 := ha.1
  have h2 : a ≠ 3 := ha.2
  
  have h3 : a + 3 > 0 := by linarith
  
  have h4 : (a - 3) ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    intro h
    apply h2
    linarith
  
  have h5 : (a + 3) * (a - 3) ^ 2 > 0 := by
    apply mul_pos
    exact h3
    exact h4
  
  nlinarith [sq_nonneg (a - 3), sq_nonneg (a), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_pos_of_ne_zero (sub_ne_zero_of_ne h2)]