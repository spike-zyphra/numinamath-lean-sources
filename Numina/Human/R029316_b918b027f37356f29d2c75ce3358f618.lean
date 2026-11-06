import Mathlib

/- The numbers of apples growing on each of six apple trees form an arithmetic sequence where the greatest number of apples growing on any of the six trees is double the least number of apples growing on any of the six trees. The total number of apples growing on all six trees is 990. Find the greatest number of apples growing on any of the six trees. -/

theorem algebra_98652 (a d : ℕ) (h₀ : a + 5 * d = 2 * a)
    (h₁ : ∑ i ∈ Finset.range 6, (a + i * d) = 990) : a + 5 * d = 220 := by
  -- Taking the sum gives us an equation in a and d
  norm_num [Finset.sum_range_succ] at h₁
  -- We have a linear system of two equations in two variables, and we solve it
  omega