import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10694 :
  IsLeast {(y : ℝ) | ∃ x, y = |(|x| - (-x^2 - 3*x - 2))|} 1 := by
  constructor
  · -- Show 1 is in the set.
    use -1
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Show 1 is the least element
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : |(|x| - (-x^2 - 3*x - 2))| ≥ 1 := by
      by_cases h : x ≥ 0
      · -- If x ≥ 0, then |x| = x.
        have h2 : |x| = x := by 
          apply abs_of_nonneg h
        have eq3 : (|x| - (-x^2 - 3*x - 2) : ℝ) = (x ^ 2 + 4 * x + 2 : ℝ) := by
          rw [h2]
          all_goals nlinarith
        have h5 : |(|x| - (-x^2 - 3*x - 2))| = |x^2 + 4 * x + 2| := by
          rw [eq3]
        have h6 : |x ^ 2 + 4 * x + 2| ≥ 1 := by
          have h7 : x ^ 2 + 4 * x + 2 ≥ -2 := by 
            nlinarith [sq_nonneg (x + 2)]
          cases' abs_cases (x ^ 2 + 4 * x + 2) with h h <;> 
            nlinarith [sq_nonneg (x + 2)]
        rw [h5]
        linarith [h6]
      · -- If x < 0, then |x| = -x.
        have h2 : |x| = -x := by 
          rw [abs_of_neg (show x < (0 : ℝ) by linarith)]
        have eq3 : (|x| - (-x^2 - 3*x - 2) : ℝ) = (x^2 + 2*x + 2 : ℝ) := by
          rw [h2]
          all_goals nlinarith
        have h5 : |(|x| - (-x^2 - 3*x - 2))| = |x^2 + 2*x + 2| := by
          rw [eq3]
        have h6 : |x ^ 2 + 2 * x + 2| ≥ 1 := by
          have h7 : x ^ 2 + 2 * x + 2 ≥ 1 := by 
            nlinarith [sq_nonneg (x + 1)]
          have h8 : |x ^ 2 + 2 * x + 2| = x ^ 2 + 2 * x + 2 := by
            rw [abs_of_nonneg (by linarith)]
          linarith [h8, h7]
        rw [h5]
        linarith [h6]
    linarith [h1, hx]