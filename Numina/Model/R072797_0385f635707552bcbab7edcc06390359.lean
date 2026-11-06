import Mathlib

theorem number_theory_250385 : (Nat.floor (10 ^ 2015 * (13 / 999 : ℝ))) % 10 = 1 := by
  have h1 : Nat.floor (10 ^ 2015 * (13 / 999 : ℝ)) = (13 * 10 ^ 2015) / 999 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num
  <;> try { native_decide }
  <;> try { ring_nf <;> omega }