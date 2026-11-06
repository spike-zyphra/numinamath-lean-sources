import Mathlib

theorem algebra_10393 : (Nat.floor (Real.sqrt 17))^2 = 16 := by
  have h1 : Nat.floor (Real.sqrt 17) = 4 := by
    have h4 : 4 < Real.sqrt 17 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h5 : Real.sqrt 17 < 5 := by
      rw [Real.sqrt_lt] <;> norm_num
    have h6 : Nat.floor (Real.sqrt 17) = 4 := by
      simp [Nat.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith
    exact h6
  calc 
    (Nat.floor (Real.sqrt 17))^2 = 4^2 := by rw [h1]
    _ = 16 := by norm_num