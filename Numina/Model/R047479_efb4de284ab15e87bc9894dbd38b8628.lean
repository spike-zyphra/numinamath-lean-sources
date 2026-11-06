import Mathlib

theorem algebra_150443 {x y z : ℤ} (h₀ : x ≠ y) (h₁ : y ≠ z) (h₂ : z ≠ x) :
    5 * (x - y) * (y - z) * (z - x) ∣ (x - y)^5 + (y - z)^5 + (z - x)^5 := by
  use x^2 + y^2 + z^2 - x * y - y * z - z * x
  ring_nf
  <;> nlinarith [sq_pos_of_ne_zero (show (x - y : ℤ) ≠ 0 by
    intro h'
    apply h₀
    have : x = y := by linarith
    assumption
  ), sq_pos_of_ne_zero (show (y - z : ℤ) ≠ 0 by 
    intro h'
    apply h₁
    have : y = z := by linarith
    assumption
  ), sq_pos_of_ne_zero (show (z - x : ℤ) ≠ 0 by 
    intro h'
    apply h₂
    have : z = x := by linarith
    assumption
  )]