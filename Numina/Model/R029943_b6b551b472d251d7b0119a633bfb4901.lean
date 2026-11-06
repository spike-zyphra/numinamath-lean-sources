import Mathlib

theorem algebra_19569 : (Nat.ceil (Real.sqrt 27) : ℕ) - (Nat.floor (Real.sqrt 26)) = 1 := by
  have h1 : 5 < Real.sqrt 27 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h2 : Real.sqrt 27 < 6 := by
    rw [Real.sqrt_lt] <;> norm_num

  have h3 : 5 < Real.sqrt 26 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h4 : Real.sqrt 26 < 6 := by
    rw [Real.sqrt_lt] <;> norm_num

  have h5 : Nat.ceil (Real.sqrt 27) = 6 := by
    have h51 : 5 < Real.sqrt 27 := h1
    have h52 : Real.sqrt 27 ≤ (6 : ℝ) := by
      linarith
    simp [Nat.ceil_eq_iff]
    constructor <;> (try norm_num) <;> try tauto
  have h6 : Nat.floor (Real.sqrt 26) = 5 := by
    have h61 : 5 ≤ Real.sqrt 26 := by
      linarith
    have h62 : Real.sqrt 26 < 6 := h4
    simp [Nat.floor_eq_iff]
    constructor <;> (try norm_num) <;> try tauto

  calc
    (Nat.ceil (Real.sqrt 27) : ℕ) - (Nat.floor (Real.sqrt 26)) = 6 - 5 := by
      rw [h5, h6]
    _ = 1 := by norm_num