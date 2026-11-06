import Mathlib

theorem number_theory_19189 : (Nat.floor (10^9 * (3 / 7 : ℝ)) % 10) = 8 := by
  have h : Nat.floor (10^9 * (3 / 7 : ℝ)) = 428571428 := by
    norm_num [Nat.floor_eq_iff]
    <;> try { norm_num }
  calc
    Nat.floor (10^9 * (3 / 7 : ℝ)) % 10
        = 428571428 % 10 := by rw [h]
    _ = 8 := by norm_num