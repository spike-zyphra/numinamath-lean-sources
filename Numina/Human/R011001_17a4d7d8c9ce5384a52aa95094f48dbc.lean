import Mathlib

/- 1. Determine all real numbers $p$ such that for any positive numbers $x, y$ the inequality


$$

\frac{x^{3}+p y^{3}}{x+y} \geqq x y

$$


holds. -/
theorem inequalities_271062 (p : ℝ) :
    (∀ x y : ℝ, x > 0 → y > 0 → (x ^ 3 + p * y ^ 3) / (x + y) ≥ x * y) ↔ p ≥ 1 := by
  constructor
  -- plug in x = y = 1 to show lhs implies p ≥ 1
  . rintro h
    specialize h 1 1 (by norm_num) (by norm_num)
    linarith
  -- to prove rhs implies lhs, write inequality using multiplications
  . rintro hp x y hx hy
    refine (le_div_iff₀ ?_).mpr ?_
    . positivity
      -- now xy(x+y) ≤ x^3 + y^3 as that is equivalent to 0 ≤ (x + y) * (x - y)^2
    . calc
        _ ≤ x^3 + y^3 := by
          have : 0 ≤ (x + y) * (x - y)^ 2 := by
            positivity
          linarith
        -- then x^3 + y^3 ≤ x^3 + p * y^3
        _ ≤ x^3 + p * y^3 := by
          gcongr
          apply le_mul_of_one_le_left
          . positivity
          . assumption