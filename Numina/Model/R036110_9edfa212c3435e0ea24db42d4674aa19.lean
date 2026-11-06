import Mathlib

theorem algebra_196661 {a b c : ℝ} (h : a ≠ 0) (h' : b ≠ 0) (h'' : c ≠ 0)
    (h''' : a + b + c = 0) :
    a * (1 / b + 1 / c) + b * (1 / a + 1 / c) + c * (1 / a + 1 / b) = -3 := by
  have h1 : c = -a - b := by linarith
  rw [h1]
  field_simp [(show b ≠ 0 by exact h'), (show a ≠ 0 by exact h), (show (-a - b) ≠ 0 by 
    by_contra h11
    have : a + b = 0 := by linarith
    have h2 : c = 0 := by linarith [h''', h11]
    contradiction
  ), (show a ≠ 0 by exact h), (show b ≠ 0 by exact h') ]
  <;> nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact h), sq_pos_of_ne_zero (show b ≠ 0 by exact h'), sq_pos_of_ne_zero (show (-a - b) ≠ 0 by 
    by_contra h11
    have : a + b = 0 := by linarith
    have h2 : c = 0 := by linarith [h''', h11]
    contradiction
  ), sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg ((-a - b) - a), sq_nonneg ((-a - b) - b) ]