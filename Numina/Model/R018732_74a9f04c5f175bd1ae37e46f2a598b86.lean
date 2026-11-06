import Mathlib

open Real Set

theorem algebra_6311 :
    IsLeast {x | ∃ a b : ℝ, x = (a ^ 4 + b ^ 4 + 2) / ((a ^ 2 - a + 1) * (b ^ 2 - b + 1))} (4 / 9) := by 
  constructor 
  · -- Show that 4/9 is in the set 
    use -1, -1 
    norm_num 
  · -- Show that 4/9 is the minimum of the set 
    intro x hx 
    rcases hx with ⟨a, b, hx⟩ 
    have h1 : a ^ 2 - a + 1 > 0 := by 
      nlinarith [sq_nonneg (a - 1 / 2)]
    have h2 : b ^ 2 - b + 1 > 0 := by 
      nlinarith [sq_nonneg (b - 1 / 2)]
    have h3 : (a ^ 4 + b ^ 4 + 2) / ((a ^ 2 - a + 1) * (b ^ 2 - b + 1)) ≥ (4 / 9) := by 
      have h_pos : (a ^ 2 - a + 1) * (b ^ 2 - b + 1) > 0 := mul_pos h1 h2 
      have h4 : (a ^ 4 + b ^ 4 + 2) ≥ (4 / 9) * ((a ^ 2 - a + 1) * (b ^ 2 - b + 1)) := by
        nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1)]
      have h11 : (a ^ 4 + b ^ 4 + 2) / ((a ^ 2 - a + 1) * (b ^ 2 - b + 1)) ≥ (4 / 9) := by 
        apply (le_div_iff₀ h_pos).mpr 
        linarith [h4]
      linarith 
    linarith [h3, hx]