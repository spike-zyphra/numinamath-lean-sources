import Mathlib

theorem algebra_21974 : (Nat.ceil (Real.sqrt 10)) + (Nat.floor (Real.sqrt 10)) = 7 := by

  have h1 : 3 < Real.sqrt 10 := by
    rw [Real.lt_sqrt] <;> norm_num

  have h2 : Real.sqrt 10 < 4 := by
    rw [Real.sqrt_lt] <;> norm_num

  have h3 : Nat.floor (Real.sqrt 10) = 3 := by
    simp [Nat.floor_eq_iff]
    constructor <;> (try norm_num) <;> try linarith [h1, h2]

  have h4 : Nat.ceil (Real.sqrt 10) = 4 := by
    simp [Nat.ceil_eq_iff]
    constructor <;> (try norm_num) <;> try linarith [h1, h2]

  calc
    (Nat.ceil (Real.sqrt 10)) + (Nat.floor (Real.sqrt 10))
        = 4 + 3 := by rw [h4, h3]
    _ = 7 := by norm_num