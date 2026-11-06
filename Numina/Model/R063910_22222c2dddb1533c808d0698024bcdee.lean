import Mathlib

theorem algebra_21683 : IsGreatest {y : ℝ | ∃ x : ℝ, x^2 + 2 * x - 15 = 0 ∧ y = (x ^ 3 - 1) / (x ^ 5 + x ^ 4 - x ^ 3 - x ^ 2)} (13 / 144) := by 
  constructor
  · -- Show 13/144 is indeed in the set
    use 3
    constructor
    · -- Verify that 3 is a root of the quadratic
      norm_num
    · -- Calculate the expression at x = 3
      norm_num
  · -- Show no value greater than 13/144 is in the set
    intro y hy
    rcases hy with ⟨x, hx2, hy⟩
    have h1 : x^2 + 2 * x - 15 = 0 := hx2
    have h2 : (x - 3) * (x + 5) = 0 := by
      linarith [h1]
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- Case x = 3
      have hx : x = 3 := by linarith
      rw [hy, hx]
      norm_num
    · -- Case x = -5
      have hx : x = -5 := by linarith
      rw [hy, hx]
      norm_num