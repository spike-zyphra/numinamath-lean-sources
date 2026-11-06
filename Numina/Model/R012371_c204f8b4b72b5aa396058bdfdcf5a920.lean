import Mathlib

theorem algebra_21501 : (Nat.floor (10^1000 * (4 / 15 : ℝ)) % 10) = 6 := by 
  have h1 : Nat.floor (10^1000 * (4 / 15 : ℝ)) = (10^1000 * 4) / 15 := by
    norm_num [Nat.floor_eq_iff]
    <;> ring_nf <;> norm_num
  rw [h1]
  norm_num