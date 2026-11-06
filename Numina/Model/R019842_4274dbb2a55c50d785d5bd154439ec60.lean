import Mathlib

theorem inequalities_326771 (a b c d : ℝ) (h : a * b * c * d > 0) :
    ∃ p : Equiv.Perm (Fin 4), 2 * (p 0 * p 2 + p 1 * p 3)^2 > (p 0^2 + p 1^2) * (p 2^2 + p 3^2) := by 
  use Equiv.refl (Fin 4)
  simp [Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_zero, pow_two]
  <;> nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c), mul_pos h (show 0 < 1 by norm_num), sq_nonneg (a^2 + b^2 - c^2 - d^2), sq_nonneg (a * c + b * d), sq_nonneg (a * d + b * c), sq_nonneg (a * b + c * d)]
  <;> try { nlinarith }
  all_goals nlinarith