import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_13488 :
  IsLeast {x : ℝ | ∃ a b c : ℝ, b > c ∧ c > a ∧ b ≠ 0 ∧ x = ((a + b)^2 + (b - c)^2 + (c - a)^2) / b^2} (4 / 3) := by
  constructor
  · -- We will now prove that 4/3 is in the set.
    use -1, 3, 1
    norm_num
  · -- We will now prove that 4/3 is minimal.
    intro x hx
    rcases hx with ⟨a, b, c, h1, h2, hb, hx⟩
    have h3 : ((a + b)^2 + (b - c)^2 + (c - a)^2) ≥ (4 / 3) * b^2 := by
      nlinarith [sq_nonneg (a + b / 3), sq_nonneg (c - b / 3), sq_nonneg (b + 3 * a), sq_nonneg (c + a), sq_nonneg (b - 3 * a), sq_nonneg (c - a), sq_nonneg (b + 3), sq_pos_of_pos (show b - c > 0 by linarith), sq_pos_of_pos (show c - a > 0 by linarith)]
    have h4 : ((a + b)^2 + (b - c)^2 + (c - a)^2) / b^2 ≥ (4 / 3) := by
      have hb2_pos : b^2 > 0 := by
        exact sq_pos_of_ne_zero hb
      apply (le_div_iff₀ hb2_pos).mpr
      linarith
    linarith [hx, h4]