import Mathlib

theorem inequalities_127228 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * y * z / (x ^ 3 + y ^ 3 + x * y * z) +
    y * z * x / (y ^ 3 + z ^ 3 + y * z * x) +
    z * x * y / (z ^ 3 + x ^ 3 + z * x * y) ≤ 1 := by

  have h1 : x * y * z / (x ^ 3 + y ^ 3 + x * y * z) ≤ z / (x + y + z) := by
    have hx1 : 0 < x ^ 3 + y ^ 3 + x * y * z := by positivity
    have hx2 : 0 < x + y + z := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    -- after cross multiplication and expand, it suffices to show:
    -- $x * y * z * (x + y + z) \leq z * (x^3 + y^3 + x * y * z)$
    -- simplifies to $x * y * (x + y + z) \leq x^3 + y^3 + x * y * z$
    -- simplifies to $x^2 * y + x * y^2 + x * y * z \leq x^3 + y^3 + x * y * z$
    -- simplifies to $x^2 * y + x * y^2 \leq x^3 + y^3$
    -- This inequality is equivalent to $x^3 - x^2 * y + y^2 * x - y^3 \geq 0$, which factors into $(x + y)(x - y)^2 \geq 0$.
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y), sq_nonneg ((x - y) * (x + y)), sq_nonneg ((x - y) * z), sq_nonneg ((x + y) * z)]
  
  have h2 : y * z * x / (y ^ 3 + z ^ 3 + y * z * x) ≤ x / (x + y + z) := by
    have hx1 : 0 < y ^ 3 + z ^ 3 + y * z * x := by positivity
    have hx2 : 0 < x + y + z := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    -- after cross multiplication and expand, it suffices to show:
    -- $y * z * x * (x + y + z) \leq x * (y^3 + z^3 + y * z * x)$
    -- simplifies to $y * z * (x + y + z) \leq 1 * (y^3 + z^3 + y * z * x)$ (after cancel positive x)
    -- simplifies to $y * z * x + y * z * y + y * z * z \leq y^3 + z^3 + y * z * x$
    -- simplifies to $y^2z + yz^2 \leq y^3 + z^3$
    -- This inequality is equivalent to $y^3 - y^2 * z + z^2 * y - z^3 \geq 0$, which factors into $(y + z)(y - z)^2 \geq 0$.
    nlinarith [sq_nonneg (y - z), sq_nonneg (y + z), sq_nonneg (y * z), sq_nonneg ((y - z) * (y + z)), sq_nonneg ((y - z) * x), sq_nonneg ((y + z) * x)]
  
  have h3 : z * x * y / (z ^ 3 + x ^ 3 + z * x * y) ≤ y / (x + y + z) := by
    have hx1 : 0 < z ^ 3 + x ^ 3 + z * x * y := by positivity
    have hx2 : 0 < x + y + z := by positivity
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    -- after cross multiplication and expand, it suffices to show:
    -- $z * x * y * (x + y + z) \leq y * (z^3 + x^3 + z * x * y)$
    -- simplifies to $z * x * (x + y + z) \leq 1 * (z^3 + x^3 + z * x * y)$ (after cancel positive y)
    -- simplifies to $z * x * x + z * x * y + z * x * z \leq z^3 + x^3 + z * x * y$
    -- simplifies to $z x^2 + x z y + z^2 x \leq z^3 + x^3 + z x y$
    -- simplifies to $x^2z + xz^2 \leq x^3 + z^3$
    -- This inequality is equivalent to $x^3 - x^2 * z + z^2 * x - z^3 \geq 0$, which factors into $(x + z)(x - z)^2 \geq 0$.
    nlinarith [sq_nonneg (z - x), sq_nonneg (z + x), sq_nonneg (z * x), sq_nonneg ((z - x) * (z + x)), sq_nonneg ((z - x) * y), sq_nonneg ((z + x) * y)]
  
  have h4 : x * y * z / (x ^ 3 + y ^ 3 + x * y * z) +
      y * z * x / (y ^ 3 + z ^ 3 + y * z * x) + z * x * y / (z ^ 3 + x ^ 3 + z * x * y) ≤ z / (x + y + z) + x / (x + y + z) + y / (x + y + z) := by
    linarith [h1, h2, h3]

  have h5 : z / (x + y + z) + x / (x + y + z) + y / (x + y + z) = 1 := by
    have hx2 : 0 < x + y + z := by positivity
    field_simp
    <;> ring
    all_goals nlinarith
  
  linarith [h4, h5]