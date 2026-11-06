import Mathlib

/- Determine the range of the real number $m$ such that the solution set of the inequality $x^2 - x \leq 0$ is a subset of the solution set for the inequality $x^2 - 4x + m \geq 0$. -/
theorem algebra_9036 (m : ℝ) :{x | x ^ 2 - x ≤ 0} ⊆ {x | x ^ 2 - 4 * x + m ≥ 0} ↔ m ≥ 3 := by
constructor
-- mp direction
simp
intro h
-- notice that x^2-4x+... = (x-2)^2 -4 +..., its minimum is at x=2
-- x^2-x ≤ 0 says 0≤x≤1, and when x=1, x^2-4x+... is at minimum.
rcases h 1 with hm
simp at hm
linarith [hm]
-- mpr direction
simp
intro hm
intro x hx
have h1: x ≤ 1 := by
    by_contra! h2
    have ht1: x^2 > x := by
        rw [pow_two]
        exact lt_mul_self h2
    have ht2: ¬ x^2 ≤ x := not_le_of_lt ht1
    contradiction
have h2: x^2 - 4*x ≥  -3 := by
    have ht1: x^2 - 4*x = (x-1)^2 + (-2*x-1) := by ring
    have ht2: (x-1)^2 ≥ 0 := sq_nonneg (x - 1)
    have ht3: (-2*x-1) ≥ -3 := by linarith [h1]
    rw [ht1]
    exact le_add_of_nonneg_of_le ht2 ht3
have h3: x^2 - 4*x + m ≥ -3 + 3 := add_le_add h2 hm
linarith [h3]