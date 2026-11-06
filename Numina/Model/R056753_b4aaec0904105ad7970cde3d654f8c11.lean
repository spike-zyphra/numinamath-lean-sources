import Mathlib

open Real Set

theorem inequalities_286586 :
    IsLeast {x | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ x = (a + b) * (1 / a + 4 / b)} 9 := by

  constructor

  · -- Show 9 is in the set
    use 1, 2
    norm_num

  · -- Show 9 is the least element
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx⟩

    have h1 : (a + b) * (1 / a + 4 / b) ≥ 9 := by
      have h2 : a * b > 0 := mul_pos ha hb
      have h3 : (a + b) * (1 / a + 4 / b) - 9 ≥ 0 := by
        have h4 : (a + b) * (1 / a + 4 / b) - 9 = (2 * a - b) ^ 2 / (a * b) := by
          field_simp
          ring
        rw [h4]
        apply div_nonneg 
        · -- Show numerator is non-negative
          apply pow_two_nonneg
        · -- Show denominator is positive
          positivity
      linarith

    linarith [hx, h1]