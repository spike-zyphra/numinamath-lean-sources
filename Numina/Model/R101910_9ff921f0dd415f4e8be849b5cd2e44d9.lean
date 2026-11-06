import Mathlib

theorem algebra_107065 (a b c d : ℤ) (hab : a ≠ b) (h : a - b ∣ a * c + b * d) :
    a - b ∣ a * d + b * c := by
  have h2 : a * d + b * c = (a * c + b * d) + (a - b) * (d - c) := by
    ring
  rw [h2]
  apply dvd_add
  exact h
  apply dvd_mul_right