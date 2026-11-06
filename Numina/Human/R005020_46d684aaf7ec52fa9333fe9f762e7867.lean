import Mathlib
/- Find the maximum value of $z+x$, if $(x, y, z, t)$ satisfies the conditions:

$$
\left\{\begin{array}{l}
x^{2}+y^{2}=4 \\
z^{2}+t^{2}=9 \\
x t+y z \geq 6
\end{array}\right.
$$ -/
theorem algebra_605095 : IsGreatest {a : ℝ| ∃ x y z t : ℝ, x ^ 2 + y ^ 2 = 4 ∧ z ^ 2 + t ^ 2 = 9 ∧ x * t + y * z ≥ 6 ∧ a = z + x} (√13):= by
  constructor
  -- First part: Prove that √13 belongs to the set by providing specific values
  -- Using x = 4/√13, y = 6/√13, z = 9/√13, t = 6/√13
  .
    simp
    use (4 / √13)
    use (6 / √13)
    constructor
    .
      field_simp
      linarith
    .
      use (9 / √13)
      use (6 / √13)
      constructor
      .
        field_simp
        linarith
      .
        constructor
        .
          field_simp
          linarith
        .
          field_simp
          linarith
  -- Second part: Prove that √13 is an upper bound
  .
    simp [upperBounds]
    intro a x y h1 z t h2 h3 h4
    subst a
    -- Use Cauchy-Schwarz inequality in the form:
    -- (x²+y²)(z²+t²) = (xt+yz)² + (xz-yt)²
    have h4 : (x ^ 2 + y ^ 2) * (z ^ 2 + t ^ 2) = (x * t + y * z) ^ 2 + (x * z - y * t) ^ 2:= by ring
    -- From the condition xt+yz ≥ 6, we know (xt+yz)² ≥ 36
    have h5 : (x * t + y * z) ^ 2 ≥ 6 ^ 2:= by nlinarith only [h3]
    rw [h1, h2] at h4
    -- This implies xz-yt = 0 using the following steps:
    replace h4 : (x * z - y * t) ^ 2 ≤ 0:= by linarith
    replace h5 : (x * z - y * t) ^ 2 ≥ 0:= by positivity
    replace h4 : (x * z - y * t) ^ 2 = 0:= by linarith
    replace h4 : x * z - y * t = 0:= by exact pow_eq_zero h4
    -- Final steps to prove x+z ≤ √13
    have h6 : (y - t) ^ 2 ≥ 0:= by positivity
    replace h5 : (x + z) ^ 2 ≤ 13:= by linarith
    rw [show 13 = (√13) ^ 2 by field_simp] at h5
    replace h5 : |x + z| ≤ |√13|:= by exact sq_le_sq.mp h5
    rw [show |√13| = √13 by field_simp] at h5
    have h7 : |x + z| ≥ x + z:= by exact le_abs_self (x + z)
    linarith
