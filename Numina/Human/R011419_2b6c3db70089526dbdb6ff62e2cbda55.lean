import Mathlib

/- 11.(RUS)Let $x, y$ , and $z$ be positive real numbers such that $x y z=1$ . Prove that
$$
\frac{x^{3}} {( 1+y ) ( 1+z )}+\frac{y^{3}} {( 1+z ) ( 1+x )}+\frac{z^{3}} {( 1+x ) ( 1+y )} \geq\frac{3} {4}.
$$ -/
theorem inequalities_24815 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z = 1) : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) ≥ 3 / 4:= by
  -- Establish that the product of denominators is positive
  have gxyz : (1 + x) * (1 + y) * (1 + z) > 0:= by positivity

  -- Rewrite the left side of the inequality with a common denominator
  have h2 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) =
  (x ^ 3 * (x + 1) + y ^ 3 * (y + 1) + z ^ 3 * (z + 1)) / ((1 + x) * (1 + y) * (1 + z)):= by
    field_simp
    linarith

  rw [h2]

  -- Convert the inequality to an equivalent form by multiplying both sides by the denominator
  suffices (x ^ 3 * (x + 1) + y ^ 3 * (y + 1) + z ^ 3 * (z + 1)) ≥ ((1 + x) * (1 + y) * (1 + z)) * (3 / 4) by exact (le_div_iff₀' gxyz).mpr this

  -- Expand the numerator
  have h3 : x ^ 3 * (x + 1) + y ^ 3 * (y + 1) + z ^ 3 * (z + 1) = (x ^ 4 + y ^ 4 + z ^ 4) + (x ^ 3 + y ^ 3 + z ^ 3):= by linarith

  -- Expand the product of (1+x)(1+y)(1+z)
  have h4 : (1 + x) * (1 + y) * (1 + z) = 1 + x * y * z + (x + y + z) + (x * y + y * z + z * x):= by ring_nf

  -- Substitute x*y*z = 1 into the expanded product
  rw [h] at h4

  -- Inequality: sum of products ≤ sum of squares
  have g1 : x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2:= by
    have g1 : (x - y) ^ 2 + (y - z) ^ 2 + (x - z) ^ 2 ≥ 0:= by positivity
    linarith

  -- Inequality relating sums of cubes and linear terms to sum of squares
  have g2 : x ^ 3 + y ^ 3 + z ^ 3 + x + y + z ≥ 2 * (x ^ 2 + y ^ 2 + z ^ 2):= by
    have g2 : x * (x - 1) ^ 2 + y * (y - 1) ^ 2 + z * (z - 1) ^ 2 ≥ 0:= by positivity
    linarith

  -- Inequality relating sum of fourth powers to sum of squares
  have g3 : x ^ 4 + y ^ 4 + z ^ 4 + 3 ≥ 2 * (x ^ 2 + y ^ 2 + z ^ 2):= by
    have g3 : (x ^ 2 - 1) ^ 2 + (y ^ 2 - 1) ^ 2 + (z ^ 2 - 1) ^ 2 ≥ 0:= by positivity
    linarith

  -- Inequality relating sum of squares to sum of linear terms
  have g4 : x ^ 2 + y ^ 2 + z ^ 2 + 3 ≥ 2 * (x + y + z):= by
    have g4 : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 ≥ 0:= by positivity
    linarith

  -- Proving that x + y + z ≥ 3 using AM-GM inequality
  have g5 : x + y + z ≥ 3:= by
    -- General lemma: for positive a,b,c, we have a³ + b³ + c³ ≥ 3abc
    have g5 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a ^ 3 + b ^ 3 + c ^ 3 ≥ a * b * c * 3:= by
      intro a b c ⟨ha, ⟨hb, hc⟩⟩
      have _ : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = (1 / 2) * (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2):= by ring_nf
      have g6 : (1 / 2) * (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ≥ 0:= by positivity
      linarith

    -- For any positive x, x^(1/3) is positive
    have gx1 : ∀ x : ℝ, x > 0 → x ^ ((1 : ℝ) / 3) > 0:= by
      intro x hx
      positivity

    -- For any positive x, (x^(1/3))^3 = x
    have gx2 : ∀ x : ℝ, x > 0 → (x ^ ((1 : ℝ) / 3)) ^ 3 = x:= by
      intro x hx
      have gx2 : (x ^ ((1 : ℝ) / 3)) ^ 3 = x ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 3):= by ring
      rw [(show x ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) = x ^ ((1 : ℝ) / 3 + 1 / 3) by exact Eq.symm (Real.rpow_add hx (1 / 3) (1 / 3))), (show (1 : ℝ) / 3 + 1 / 3 = (2 : ℝ) / 3 by ring_nf)] at gx2
      rw [(show x ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) = x ^ ((2 : ℝ) / 3 + 1 / 3) by exact Eq.symm (Real.rpow_add hx (2 / 3) (1 / 3))), (show (2 : ℝ) / 3 + 1 / 3 = 1 by ring_nf)] at gx2
      rw [gx2]
      simp

    -- Since x*y*z = 1, we have x^(1/3) * y^(1/3) * z^(1/3) = 1
    have gx3 : x ^ ((1 : ℝ) / 3) * y ^ ((1 : ℝ) / 3) * z ^ ((1 : ℝ) / 3) = 1:= by
      rw [show x ^ ((1 : ℝ) / 3) * y ^ ((1 : ℝ) / 3) = (x * y) ^ ((1 : ℝ) / 3) by refine Eq.symm (Real.mul_rpow (by linarith) (by linarith)), show (x * y) ^ ((1 : ℝ) / 3) * z ^ ((1 : ℝ) / 3) = (x * y * z) ^ ((1 : ℝ) / 3) by refine Eq.symm (Real.mul_rpow (by positivity) (by linarith))]
      simp [h]

    -- Apply the lemma to x^(1/3), y^(1/3), z^(1/3)
    specialize g5 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) ⟨(gx1 x hx), ⟨(gx1 y hy), (gx1 z hz)⟩⟩
    rw [(gx2 x hx), (gx2 y hy), (gx2 z hz), gx3] at g5
    linarith

  -- Rewrite expressions and combine all inequalities to complete the proof
  rw [h3, h4]
  clear h2 h3 h4
  linarith
