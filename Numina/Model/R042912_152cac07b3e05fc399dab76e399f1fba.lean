import Mathlib

theorem algebra_1716 {x y z : ℤ} (h₀ : x ≠ y) (h₁ : x ≠ z) (h₂ : y ≠ z) (h₃ : x * y + x * z + y * z = 26) :
    x ^ 2 + y ^ 2 + z ^ 2 ≥ 29 := by
  have h4 : (x - y) ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    intro h'
    apply h₀
    linarith 
  have h5 : (x - z) ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    intro h'
    apply h₁
    linarith 
  have h6 : (y - z) ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    intro h'
    apply h₂
    linarith 
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y + z)]