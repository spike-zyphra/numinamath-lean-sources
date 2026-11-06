import Mathlib

theorem algebra_292745 {a b c : ℝ} (h : a ≠ -b ∧ b ≠ -c ∧ c ≠ -a) (h' : (a - c) / (b + c) + (b - a) / (a + c) + (c - b) / (b + a) = 1) :
    (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) = 4 := by
  rcases h with ⟨h1, h2, h3⟩
  have h4 : b + c ≠ 0 := by
    intro h'
    apply h2
    linarith
  have h5 : a + c ≠ 0 := by
    intro h'
    apply h3
    linarith
  have h6 : b + a ≠ 0 := by
    intro h'
    apply h1
    linarith
  field_simp [(show b + c ≠ 0 by exact h4), (show a + c ≠ 0 by exact h5), (show b + a ≠ 0 by exact h6)] at h'
  field_simp [(show b + c ≠ 0 by exact h4), (show c + a ≠ 0 by
    intro h'
    apply h3
    linarith
  ), (show a + b ≠ 0 by 
    intro h'
    apply h1
    linarith
  )]
  <;> nlinarith [sq_pos_of_ne_zero (show (a + b) ≠ 0 by 
    intro h'
    apply h1
    linarith
  ), sq_pos_of_ne_zero (show (b + c) ≠ 0 by
    intro h'
    apply h2
    linarith
  ), sq_pos_of_ne_zero (show (a + c) ≠ 0 by 
    intro h'
    apply h3
    linarith
  ), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]