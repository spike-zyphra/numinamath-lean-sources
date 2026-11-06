import Mathlib

theorem algebra_31294 (a b c : ℝ) (h : (a - b) * (b - c) * (c - a) ≠ 0) :
    b^2 * c^2 / ((a - b) * (a - c)) + c^2 * a^2 / ((b - c) * (b - a)) +
    a^2 * b^2 / ((c - a) * (c - b)) = a * b + b * c + c * a := by
  have h1 : a - b ≠ 0 := by
    by_contra h1
    have : (a - b) * (b - c) * (c - a) = 0 := by
      rw [h1]
      norm_num
    contradiction
  have h2 : b - c ≠ 0 := by
    by_contra h2
    have : (a - b) * (b - c) * (c - a) = 0 := by
      rw [h2]
      norm_num
    contradiction
  have h3 : c - a ≠ 0 := by
    by_contra h3
    have : (a - b) * (b - c) * (c - a) = 0 := by
      rw [show c - a = 0 by linarith]
      norm_num
    contradiction
  have h4 : a - c ≠ 0 := by
    by_contra h4
    have : c - a = 0 := by
      linarith
    contradiction
  have h5 : b - a ≠ 0 := by
    by_contra h5
    have : a - b = 0 := by
      linarith
    contradiction
  have h6 : c - b ≠ 0 := by
    by_contra h6
    have : b - c = 0 := by
      linarith
    contradiction

  field_simp [(show (a - b) ≠ 0 by assumption), (show (a - c) ≠ 0 by
    intro h7
    apply h4
    linarith
  ), (show (b - c) ≠ 0 by assumption), (show (b - a) ≠ 0 by
    intro h7
    apply h5
    linarith
  ), (show (c - a) ≠ 0 by assumption), (show (c - b) ≠ 0 by
    intro h7
    apply h6
    linarith
  )]

  ring_nf
  <;> 
  field_simp [(show (a - b) ≠ 0 by assumption), (show (a - c) ≠ 0 by
    intro h7
    apply h4
    linarith
  ), (show (b - c) ≠ 0 by assumption), (show (b - a) ≠ 0 by
    intro h7
    apply h5
    linarith
  ), (show (c - a) ≠ 0 by assumption), (show (c - b) ≠ 0 by
    intro h7
    apply h6
    linarith
  )]

  <;> 
  nlinarith [sq_pos_of_ne_zero (show (a - b) * (b - c) * (c - a) ≠ 0 by assumption), 
    sq_pos_of_ne_zero (show a - b ≠ 0 by assumption), 
    sq_pos_of_ne_zero (show b - c ≠ 0 by assumption), 
    sq_pos_of_ne_zero (show c - a ≠ 0 by assumption), 
    sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (a * b - c * a)
  ]