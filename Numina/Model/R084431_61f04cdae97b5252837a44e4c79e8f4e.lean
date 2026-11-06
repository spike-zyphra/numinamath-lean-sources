import Mathlib

theorem number_theory_9902: (Nat.floor ((10^93:ℚ) / (10^31 + 3)) % 100 = 8) := by
  have h1 : Nat.floor ((10^93 : ℚ) / (10^31 + 3)) = (10^93) / (10^31 + 3) := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num
  <;> native_decide