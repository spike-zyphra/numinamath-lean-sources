import Mathlib

open Real

  theorem calculus_148597 : ∫ x in (0)..1, 1 / (1 + x ^ 2) = Real.pi / 4 := by
  have h1 : ∫ x in (0)..1, 1 / (1 + x ^ 2) = Real.arctan 1 - Real.arctan 0 := by 
    norm_num [intervalIntegral.integral_const, Real.arctan]
    all_goals norm_num
  rw [h1]
  have h2 : Real.arctan 1 = Real.pi / 4 := Real.arctan_one
  have h3 : Real.arctan 0 = (0 : Real) := by
    simp [Real.arctan_zero]
  rw [h2, h3]
  all_goals norm_num