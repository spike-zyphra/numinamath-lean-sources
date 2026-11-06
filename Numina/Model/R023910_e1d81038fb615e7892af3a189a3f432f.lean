import Mathlib

theorem number_theory_7853 : 3 * ⌊Real.sqrt 6 - 1⌋ + 2 * (Real.sqrt 6 - 1 - ⌊Real.sqrt 6 - 1⌋) = 2 * Real.sqrt 6 - 1 := by
  have h1 : ⌊Real.sqrt 6 - 1⌋ = 1 := by
    have h2 : 2 < Real.sqrt 6 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h3 : Real.sqrt 6 < 3 := by
      rw [Real.sqrt_lt] <;> norm_num
    have h4 : 1 < Real.sqrt 6 - 1 := by
      linarith
    have h5 : Real.sqrt 6 - 1 < 2 := by
      linarith
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try linarith
  rw [h1]
  ring