import Mathlib

/- 2. For the quadratic trinomial $p(x)=(a+1) x^{2}-(a+1) x+2022$, it is known that $-2022 \leq p(x) \leq 2022$ for $x \in[0 ; 1]$. Find the greatest possible value of $a$. -/
theorem algebra_234731 :
    IsGreatest {a : ℝ | ∀ x ∈ Set.Icc 0 1, -2022 ≤ (a + 1) * x ^ 2 - (a + 1) * x + 2022 ∧
    (a + 1) * x ^ 2 - (a + 1) * x + 2022 ≤ 2022} 16175 := by
  constructor
  -- to show such 16175 is in the set, assume x in [0, 1]
  . simp
    rintro x hx_lb hx_ub
    ring_nf
    and_intros
    -- first inquality is equivalent to following, which is obivously true
    . suffices 0 ≤ 16176 * (x - 1/2)^2 by linarith
      positivity
    -- second inequality is equivalent to 0 ≤  x * (1-x) which is true on [0, 1]
    . suffices 0 ≤ x * (1 - x) by linarith
      apply mul_nonneg <;> linarith
  -- to show it's an upperbound, write the quadratic equation by compleating the square
  . rintro a ha
    simp at ha
    have (x : ℝ) : (a + 1) * x ^ 2 - (a + 1) * x + 2022 =
        (a + 1) * (x - 1/2)^2 + (2022 - a/4 - 1/4) := by ring
    -- at 1/2, the left inequality gives us desiered upper bound on a
    specialize ha (1/2) (by norm_num) (by norm_num)
    replace ha := ha.left
    rw [this] at ha
    simp at ha
    linarith