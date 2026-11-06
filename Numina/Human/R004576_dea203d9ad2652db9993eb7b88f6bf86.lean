import Mathlib
/- 1. It is given that $x, y, z$ are 3 real numbers such that
$$
\frac{x-y}{2+x y}+\frac{y-z}{2+y z}+\frac{z-x}{2+z x}=0 .
$$

Is it true that at least two of the three numbers must be equal? Justify your answer. -/
theorem number_theory_286001 (x y z : ℝ) (h1 : 2 + x * y ≠ 0) (h2 : 2 + y * z ≠ 0) (h3 : 2 + z * x ≠ 0) (h : (x - y) / (2 + x * y) + (y - z) / (2 + y * z) + (z - x) / (2 + z * x) = 0) : x = y ∨ y = z ∨ z = x:= by
  -- Multiply both sides by the product of all denominators to clear fractions
  replace h : (2 + x * y) * (2 + y * z) * (2 + z * x) * ((x - y) / (2 + x * y) + (y - z) / (2 + y * z) + (z - x) / (2 + z * x)) = 0:= by rw [h] ; simp
  -- Simplify the left side using field operations and ring normalization
  rw [show (2 + x * y) * (2 + y * z) * (2 + z * x) * ((x - y) / (2 + x * y) + (y - z) / (2 + y * z) + (z - x) / (2 + z * x))  = 2 * (x - y) * (y - z) * (z - x) by field_simp ; ring_nf] at h
  -- Simplify to get that the product of differences equals zero
  simp at h
  -- Case analysis: if a product equals zero, at least one factor must be zero
  rcases h with h | h
  .
    -- Case where (x - y) = 0 or (y - z) = 0
    rcases h with h | h
    .
      -- If x - y = 0, then x = y
      replace h : x = y:= by linarith
      subst x
      simp
    .
      -- If y - z = 0, then y = z
      replace h : y = z:= by linarith
      subst y
      simp
  .
    -- If z - x = 0, then z = x
    replace h : z = x:= by linarith
    subst z
    simp
