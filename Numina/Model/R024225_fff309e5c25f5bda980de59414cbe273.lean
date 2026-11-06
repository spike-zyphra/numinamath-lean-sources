import Mathlib

theorem algebra_301442 {a b c : ℝ} (h : a^2 * (b + c) = 2010) (h' : b^2 * (a + c) = 2010)
    (h'' : a ≠ b) : c^2 * (a + b) = 2010 := by
  have eq1 : a ^ 2 * (b + c) = b ^ 2 * (a + c) := by 
    linarith
  have eq2 : (a - b) * (a * b + c * (a + b)) = 0 := by
    nlinarith [eq1]
  cases' (mul_eq_zero.mp eq2) with h1 h2
  · -- Assume h1 : a - b = 0 
    exfalso 
    apply h''
    linarith 
  · -- Assume h2 : a * b + c * (a + b) = 0 
    have eq3 : a * b + c * (a + b) = 0 := by
      linarith 
    have eq4 : c ^ 2 * (a + b) = 2010 := by
      have eq5 : a * b + c * (a + b) = 0 := eq3
      have eq6 : a^2 * (b + c) + b^2 * (a + c) = 4020 := by 
        linarith 
      nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by 
          intro h1
          apply h''
          linarith
        ), sq_nonneg (a - b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (c * (a + b)), sq_nonneg (a * c), sq_nonneg (b * c)]
    linarith [eq4]