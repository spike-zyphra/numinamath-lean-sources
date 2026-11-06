import Mathlib

theorem algebra_287742 :
    IsGreatest {x | ∃ a b c : ℝ, a^2 + b^2 + c^2 = 9 ∧ x = (a - b)^2 + (b - c)^2 + (c - a)^2} 27 := by
  constructor
  · -- Let's show that 27 is indeed in the set
    use Real.sqrt (3 / 2), Real.sqrt (3 / 2), -2 * Real.sqrt (3 / 2)
    constructor
    · -- Show that the sum of squares is 9.
      have h1 : (Real.sqrt (3 / 2)) ^ 2 = 3 / 2 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      nlinarith [h1]
    · -- Show that the expression equals 27
      have h1 : (Real.sqrt (3 / 2)) ^ 2 = 3 / 2 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      nlinarith [h1]
  · -- Let's show that 27 is the maximum in the set
    intro x hx
    rcases hx with ⟨a, b, c, h1, h2⟩
    nlinarith [sq_nonneg (a + b + c)]