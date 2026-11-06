import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_116822 :
  IsLeast {x : ℝ | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ x = (a + b) * (a + 2) * (b + 2) / (16 * a * b)} 1 := by
  constructor
  · -- Show that 1 is achievable
    use 2, 2
    norm_num
  · -- Show that 1 is a lower bound
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx⟩
    have h : (a + b) * (a + 2) * (b + 2) ≥ 16 * a * b := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (a*b - 4), sq_nonneg (a - b), sq_nonneg (a * b - 4*a), sq_nonneg (a * b - 4*b), mul_pos ha hb, sq_nonneg (a + b - 4)]
    have h2 : (a + b) * (a + 2) * (b + 2) / (16 * a * b) ≥ 1 := by
      apply (le_div_iff₀ (by positivity : 16 * a * b > 0)).mpr
      nlinarith
    linarith [hx, h2]