import Mathlib

theorem number_theory_222633 : (Nat.floor ((10^93 : ℝ) / (10^31 + 3)) % 100) = 8 := by
  have h : Nat.floor ((10^93 : ℝ) / (10^31 + 3)) = (10 ^ 93) / (10 ^ 31 + 3) := by
    norm_num [Nat.floor_eq_iff]
  rw [h]
  norm_num
  <;> try { omega }