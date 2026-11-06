import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_6686 :
  IsLeast {x : ℝ | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ a + b = 2 ∧ x = (a ^ 2 + b) / (a + 1) + (b ^ 2 + a) / (b + 1)} 2 := by 
  constructor
  · -- First, we will show 2 is in the set
    use 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Now, we need to show there is no value less than 2 in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hsum, hx⟩
    have h1 : b = 2 - a := by linarith
    have h2 : x = (a ^ 2 + b) / (a + 1) + (b ^ 2 + a) / (b + 1) := by linarith [hx]
    rw [h2, h1]
    have h3 : a + 1 > 0 := by nlinarith
    have h4 : (2 - a) + 1 > 0 := by nlinarith
    have h5 : (a ^ 2 + (2 - a)) / (a + 1) + ((2 - a) ^ 2 + a) / ((2 - a) + 1) ≥ 2 := by
      have h6 : 0 < a := ha
      have h7 : 0 < 2 - a := by nlinarith
      have h8 : 0 < (a + 1) * ((2 - a) + 1) := by positivity
      have h9 : (a ^ 2 + (2 - a)) / (a + 1) + ((2 - a) ^ 2 + a) / ((2 - a) + 1) - (2 : ℝ) ≥ 0 := by
        have h10 : (a ^ 2 + (2 - a)) / (a + 1) + ((2 - a) ^ 2 + a) / ((2 - a) + 1) - (2 : ℝ) = 
          ((a ^ 2 + (2 - a)) * ((2 - a) + 1) + ((2 - a) ^ 2 + a) * (a + 1) - 2 * (a + 1) * ((2 - a) + 1)) / ((a + 1) * ((2 - a) + 1)) := by 
          field_simp
          <;> ring
        rw [h10] at *
        have h11 : ((a ^ 2 + (2 - a)) * ((2 - a) + 1) + ((2 - a) ^ 2 + a) * (a + 1) - 2 * (a + 1) * ((2 - a) + 1)) ≥ 0 := by
          nlinarith [sq_nonneg (a - 1), sq_nonneg ((2 - a) - 1), sq_nonneg (a * ((2 - a))), 
            mul_pos ha (show 0 < (2 - a) by nlinarith)]
        apply div_nonneg 
        linarith
        positivity
      linarith
    linarith