import Mathlib

theorem algebra_11043 : (Nat.floor (Real.sqrt 12))^2 = 9 := by
  have h1 : Nat.floor (Real.sqrt 12) = 3 := by
    have h2 : 3 ≤ Real.sqrt 12 := by
      rw [Real.le_sqrt] <;> norm_num
    have h3 : Real.sqrt 12 < 4 := by
      rw [Real.sqrt_lt] <;> norm_num
    have h4 : Nat.floor (Real.sqrt 12) = 3 := by
      simp [Nat.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith [h2, h3]
    exact h4
  calc
    (Nat.floor (Real.sqrt 12)) ^ 2 = 3 ^ 2 := by rw [h1]
    _ = 9 := by norm_num