import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_18945 (f : ℝ → ℝ) (hf : f = λ x => (1 / 2) * x ^ 2 - 9) :
    IsLeast {d | ∃ x y, d = x ^ 2 + y ^ 2 ∧ y = f x} 17 := by
  constructor
  · -- Show 17 is in the set
    use 4
    use -1
    constructor
    · norm_num
    · -- Show that $y = f x$
      rw [hf]
      norm_num
      all_goals norm_num
  · -- Show that 17 is least
    intro d hd
    rcases hd with ⟨x, y, h_eq, hy⟩
    have h1 : y = (1 / 2) * x ^ 2 - 9 := by 
      rw [hy]
      rw [hf]
      all_goals norm_num
    rw [h_eq, h1]
    nlinarith [sq_nonneg (x ^ 2 - 16), sq_nonneg (x + 4), sq_nonneg (x - 4), sq_nonneg (x * x - 16), sq_nonneg (x ^ 2 - 16)]