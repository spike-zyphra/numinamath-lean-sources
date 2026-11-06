import Mathlib

/- If $x-y=1$ and $x^2+y^2=7$, find $x^3-y^3$. -/
theorem algebra_20393 {x y : ℝ} (h₀ : x - y = 1) (h₁ : x ^ 2 + y ^ 2 = 7) :
    x ^ 3 - y ^ 3 = 10 := by
  calc _ = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring -- Use the formula for the difference of cubes
       _ = x ^ 2 + x * y + y ^ 2 := by simp [h₀] -- Simplify the expression using h₀
       _ = ((x ^ 2 + y ^ 2) * 3 - (x - y) ^ 2) / 2 := by ring -- Express the result in terms of h₁ and h₀
       _ = (7 * 3 - 1 ^ 2) / 2 := by rw [h₁, h₀] -- Substitute the values of h₁ and h₀
       _ = 10 := by norm_num -- Simplify the final expression
