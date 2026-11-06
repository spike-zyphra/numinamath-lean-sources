import Mathlib

theorem number_theory_273098 (a b c d : ℤ) (h : a - c ∣ a * b + c * d) : (a - c) ∣ a * d + b * c := by
  have h3 : a * d + b * c = (a * b + c * d) - (a - c) * (b - d) := by
    ring
  rw [h3]
  apply dvd_sub
  exact h
  apply dvd_mul_of_dvd_left
  exact dvd_refl (a - c)