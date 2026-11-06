import Mathlib

/- Prove that

$$
\sum_{c y c}(x+y) \sqrt{(z+x)(z+y)} \geq 4(x y+y z+z x),
$$

for all positive real numbers $x, y$ and $z$. -/
theorem algebra_604232 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y) * √((z + x) * (z + y)) + (y + z) * √((x + y) * (x + z)) + (z + x) * √((y + z) * (y + x)) ≥ 4 * (x * y + y * z + z * x):= by
  -- First, prove a helper lemma that shows one term is greater than or equal to a specific combination
  -- For any positive x, y, z: (x + y)√((z + x)(z + y)) ≥ 2xy + yz + zx
  have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → (x + y) * √((z + x) * (z + y)) ≥ 2 * x * y + y * z + z * x:= by
    intro x y z hx hy hz
    -- Show that the right side is non-negative
    have h1 : 2 * x * y + y * z + z * x ≥ 0:= by positivity
    -- Square both sides and prove the inequality
    have h2 : ((x + y) * √((z + x) * (z + y))) ^ 2 ≥ (2 * x * y + y * z + z * x) ^ 2:= by
      -- Rearrange the left side using ring properties
      rw [show ((x + y) * √((z + x) * (z + y))) ^ 2 = (x + y) ^ 2 * (√((z + x) * (z + y))) ^ 2 by ring]
      -- Simplify the square of the square root
      rw [show (√((z + x) * (z + y))) ^ 2 = (z + x) * (z + y) by refine Real.sq_sqrt (by positivity)]
      -- The key inequality reduces to showing (xy + yz + zx)(x-y)² ≥ 0
      suffices (x * y + y * z + z * x) * (x - y) ^ 2 ≥ 0 by linarith
      positivity
    -- Convert squared inequality back to original form
    apply sq_le_sq.1 at h2
    -- Remove absolute value signs since terms are non-negative
    rw [show |2 * x * y + y * z + z * x| = 2 * x * y + y * z + z * x by exact abs_of_nonneg h1] at h2
    rw [show |(x + y) * √((z + x) * (z + y))| = (x + y) * √((z + x) * (z + y)) by exact abs_of_nonneg (by positivity)] at h2
    exact h2
  -- Apply the helper lemma to all cyclic permutations of x, y, z
  have h2:= h1 x y z hx hy hz
  have h3:= h1 y z x hy hz hx
  have h4:= h1 z x y hz hx hy
  -- Combine the three inequalities to prove the main theorem
  linarith
