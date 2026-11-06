import Mathlib

/-What is the largest number $c$ such that $2x^2+5x+c=0$ has at least one real solution? Express your answer as a common fraction.-/
theorem algebra_21330 : IsGreatest { c : ℝ | ∃x, 2 * x^2 + 5 * x + c = 0 } (25 / 8) := by
  constructor
  · -- Prove that 25/8 is in the set
    simp
    use -5 / 4
    norm_num
  · -- Prove that 25/8 is the greatest element in the set
    apply mem_upperBounds.mpr
    simp
    intro c x hx
    have : 0 ≤ discrim 2 5 c := by
      -- A quadratic has roots if and only if its discriminant equals some square.
      rw [pow_two] at hx
      rw [discrim_eq_sq_of_quadratic_eq_zero hx]
      positivity
    rw [discrim] at this
    nlinarith
