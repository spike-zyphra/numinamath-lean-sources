import Mathlib

theorem calculus_185863 : ∫ x in (-1)..1, ∫ _y in (x^2)..1, ∫ z in (0)..2, (4 + z) = 40 / 3 := by

  have eq3 : ∫ z in (0)..2, (4 + z) = 10 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp [intervalIntegral.integral_const, integral_id]
    all_goals norm_num
  
  have eq2 : ∀ x : ℝ, ∫ y in (x^2)..1, ∫ z in (0)..2, (4 + z) = 10 * (1 - x^2) := by
    intro x
    simp [eq3]
    all_goals 
      try {
        norm_num [intervalIntegral.integral_const]
        <;> ring 
      }

  simp_rw [eq2]
  norm_num [intervalIntegral.integral_const, mul_comm]