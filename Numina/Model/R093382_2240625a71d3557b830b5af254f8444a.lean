import Mathlib

theorem number_theory_283293 : (Nat.floor (10 ^ 2008 * (2 / 13 : ℝ)) % 10) = 8 := by
  have h1 : Nat.floor (10 ^ 2008 * (2 / 13 : ℝ)) = (2 * 10 ^ 2008) / 13 := by
    norm_num [Nat.floor_eq_iff]
    <;> ring_nf <;> omega
  rw [h1]
  norm_num
  <;> ring_nf <;> omega