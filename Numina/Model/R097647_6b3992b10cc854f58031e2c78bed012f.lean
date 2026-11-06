import Mathlib

open Real

theorem algebra_2455 {a : ℝ} (A : ℝ) (hA : A = sqrt ((a^2 + 9)^4)) :
    sqrt (sqrt A) = sqrt (a^2 + 9) := by
  have h1 : A = (a^2 + 9) ^ 2 := by
    rw [hA]
    have h2 : sqrt ((a^2 + 9) ^ 4) = (a^2 + 9) ^ 2 := by
      rw [show (a^2 + 9) ^ 4 = ((a^2 + 9) ^ 2) ^ 2 by ring]
      rw [Real.sqrt_sq]
      all_goals
        nlinarith [sq_nonneg a]
    rw [h2]
  rw [h1]
  have h3 : sqrt ((a^2 + 9) ^ 2) = a^2 + 9 := by
    rw [Real.sqrt_sq]
    all_goals
      nlinarith [sq_nonneg a]
  rw [h3]