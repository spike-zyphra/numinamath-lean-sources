import Mathlib

open Real Set
open scoped Real

theorem algebra_185507 : arctan 1 + arctan (1/2) + arctan (1/3) = π/2 := by
  have h1 : arctan 1 = Real.pi / 4 := by
    rw [arctan_one]
  have h2 : arctan (1 / 2) + arctan (1 / 3) = Real.pi / 4 := by
    have h : arctan (1 / 2) + arctan (1 / 3) = arctan ( (1 / 2 + 1 / 3) / (1 - (1 / 2) * (1 / 3) ) ) := by
      rw [arctan_add]
      all_goals norm_num
    rw [h]
    have h3 : (1 / 2 + 1 / 3 : ℝ) / (1 - (1 / 2) * (1 / 3) ) = 1 := by
      norm_num
    rw [h3]
    have h4 : arctan (1 : ℝ) = Real.pi / 4 := by
      rw [arctan_one]
    rw [h4]
  linarith [h1, h2]