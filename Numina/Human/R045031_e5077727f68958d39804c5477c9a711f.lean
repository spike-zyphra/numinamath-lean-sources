import Mathlib

/- Example 10 Let $x, y, z$ be real numbers, and satisfy $x+y+z=a$, $x^{2}+y^{2}+z^{2} \leq \frac{a^{2}}{2}(a>0)$, prove that $0 \leq x \leq \frac{2}{3} a, 0 \leq y \leq \frac{2}{3} a$, $0 \leq z \leq \frac{2}{3} a$. -/
theorem inequalities_602731 (a : ℝ) (ha : 0 < a) (x y z : ℝ)
    (h₀ : x + y + z = a) (h₁ : x^2 + y^2 + z^2 ≤ (a^2) / 2) :
    0 ≤ x ∧ x ≤ (2 * a) / 3 ∧ 0 ≤ y ∧ y ≤ (2 * a) / 3 ∧ 0 ≤ z ∧ z ≤ (2 * a) / 3 := by
    -- Split the goal into 6 subgoals (0 ≤ x, x ≤ 2a/3, 0 ≤ y, y ≤ 2a/3, 0 ≤ z, z ≤ 2a/3)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    -- For all subgoals, use nonlinear arithmetic with the following facts:
    -- 1. Squares of differences are non-negative: (x-y)², (y-z)², (z-x)²
    -- 2. The sum constraint: x + y + z = a
    -- 3. The sum of squares constraint: x² + y² + z² ≤ a²/2
    -- 4. a² > 0 (since a > 0)
    all_goals
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                h₀, h₁, mul_pos ha ha]
