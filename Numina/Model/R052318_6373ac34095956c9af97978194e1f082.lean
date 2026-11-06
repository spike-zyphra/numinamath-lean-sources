import Mathlib

theorem algebra_13957 {x y : ℝ} (h : x - y = 12) : x ^ 3 - y ^ 3 - 36 * x * y = 1728 := by 
  -- Use the identity for the difference of cubes $x^3 - y^3 = (x - y)(x^2 + xy + y^2)$
  have h1 : x - y = 12 := h 
  -- Let $h2$ be that formula 
  have h2 : x ^ 3 - y ^ 3 = (x - y) * (x^2 + x * y + y^2) := by 
    ring 
  -- Now the original expression $x^3 - y^3 - 36xy$ = $(x - y)(x^2 + xy + y^2) - 36xy$ and substitute $x - y = 12$
  rw [h2]
  have h3 : (x - y) = 12 := h1 
  rw [h3]
  -- After substitution we get $12(x^2 + xy + y^2) - 36xy$
  -- Simplify $12(x^2 + x*y + y^2) - 36*x*y = 12*(x^2 - 2*x*y + y^2) = 12*(x - y)^2$
  have h4 : (x - y)^2 = 144 := by
    rw [h3]
    norm_num 
  -- Now compute $12*(144)$
  nlinarith [h4, sq_nonneg (x - y)]