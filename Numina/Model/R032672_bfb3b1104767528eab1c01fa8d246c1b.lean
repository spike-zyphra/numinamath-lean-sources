import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_31269 :
  IsGreatest {x | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 1 ∧ x = 1/(a^2 - 4*a + 9) + 1/(b^2 - 4*b + 9) + 1/(c^2 - 4*c + 9)} (7/18) := by
  constructor
  · -- Show that 7/18 is in the set.
    use 1, (0 : ℝ), (0 : ℝ)
    norm_num
  · -- Show that 7/18 is the greatest element in the set.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    have h2 : 1/(a^2 - 4*a + 9) + 1/(b^2 - 4*b + 9) + 1/(c^2 - 4*c + 9) ≤ 7/18 := by
      have h3 : a ≥ 0 := by linarith
      have h4 : b ≥ 0 := by linarith
      have h5 : c ≥ 0 := by linarith
      have h6 : a + b + c = 1 := h1
      have h7 : 1/(a^2 - 4*a + 9) ≤ 1/6 + (1/18)*(a - 1) := by
        apply (div_le_iff₀ (by nlinarith)).mpr
        nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 3)]
      have h8 : 1/(b^2 - 4*b + 9) ≤ 1/6 + (1/18)*(b - 1) := by
        apply (div_le_iff₀ (by nlinarith)).mpr
        nlinarith [sq_nonneg (b - 1), sq_nonneg (b - 3)]
      have h9 : 1/(c^2 - 4*c + 9) ≤ 1/6 + (1/18)*(c - 1) := by
        apply (div_le_iff₀ (by nlinarith)).mpr
        nlinarith [sq_nonneg (c - 1), sq_nonneg (c - 3)]
      have h10 : 1/(a^2 - 4*a + 9) + 1/(b^2 - 4*b + 9) + 1/(c^2 - 4*c + 9) ≤ (1/6 + (1/18)*(a - 1)) + (1/6 + (1/18)*(b - 1)) + (1/6 + (1/18)*(c - 1)) := by
        linarith [h7, h8, h9]
      have h11 : (1/6 + (1/18)*(a - 1)) + (1/6 + (1/18)*(b - 1)) + (1/6 + (1/18)*(c - 1)) = 7/18 := by
        nlinarith [h1]
      linarith [h10, h11]
    linarith [hx, h2]