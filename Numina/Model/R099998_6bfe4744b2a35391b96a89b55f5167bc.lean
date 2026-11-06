import Mathlib

theorem algebra_276489 {P Q : ℚ} (hP : P = 3^2000 + 3^(-2000 : ℤ)) (hQ : Q = 3^2000 - 3^(-2000 : ℤ)) :
    P^2 - Q^2 = 4 := by
  rw [hP, hQ]
  norm_num