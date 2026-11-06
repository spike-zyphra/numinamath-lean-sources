import Mathlib

/- Real numbers $x$ and $y$ have an arithmetic mean of 7 and a geometric mean of $\sqrt{19}$. Find $x^2+y^2$. -/
theorem algebra_21411 {x y : ℝ} (h₁ : (x + y) / 2 = 7) (h₂ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 := by
  -- We have x + y = 14
  replace h₁ : x + y = 14 := by linarith only [h₁]
  -- We prove x * y > 0
  have H : x * y > 0 := by
    -- Otherwise, √(x * y) = 0
    by_contra! H
    rw [Real.sqrt_eq_zero_of_nonpos H] at h₂
    -- But √19 is positive
    absurd h₂
    positivity
  apply le_of_lt at H
  -- We get x * y = 19 from the injectivity of √
  rw [Real.sqrt_inj H (by norm_num)] at h₂
  -- We have x^2 + y^2 = (x + y)^2 - 2 * x * y
  calc _ = (x + y) ^ 2 - 2 * (x * y) := by ring
       _ = 14 ^ 2 - 2 * 19 := by rw [h₁, h₂]
       _ = 158 := by norm_num
