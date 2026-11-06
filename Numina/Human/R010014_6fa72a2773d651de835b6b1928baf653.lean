import Mathlib

/- If $x-y=6$ and $x^2+y^2=24$, find $x^3-y^3$. -/
theorem algebra_20209 {x y : ℝ} (h₀ : x - y = 6) (h₁ : x ^ 2 + y ^ 2 = 24) :
    x ^ 3 - y ^ 3 = 108 := by
  -- First, we note  \[x^3-y^3 = (x-y)(x^2 +xy +y^2) = 6(24+xy),\]
  have eq1 : x ^ 3 - y ^ 3 = 6 * (24 + x * y) := by
    calc
      _ = (x - y) * (x ^ 2 + y ^ 2 + x * y) := by
        ring
      _ = _ := by
        rw [h₀, h₁]
  -- Squaring both sides of $x-y=6$ gives  $x^2 - 2xy + y^2 = 36$.
  have eq2 : x ^ 2 + y ^ 2 - 2 * x * y = 36 := by
    calc
      _ = (x - y) ^ 2 := by
        ring
      _ = _ := by
        rw [h₀]
        norm_num
  -- Since $x^2 + y^2 = 24$, we have $24-2xy = 36$, so $xy = -6$
  have eq3 : x * y = -6 := by
    rw [h₁] at eq2
    linarith
  -- $x^3-y^3 = 6(24 +xy) = 6(24 - 6) = 6(18) = \boxed{108}$
  rw [eq1, eq3]
  norm_num