import Mathlib

/- Suppose $z$ is a complex number such that $z^4 = \frac{64}{5}-\frac{48}{5}i$.  Find $|z|$.-/
theorem algebra_21543 (z : ℂ) (hz : z ^ 4 = 64 / 5 - 48 / 5 * .I) : ‖z‖ = 2 := by
  --We have that
  --\[\left|\frac{64}{5}-\frac{48}{5}i \right|= \left|\frac{16}{5}(4-3i)\right| = \frac{16}{5}|4-3i| = \frac{16}{5}(5) = 16.\]
  apply_fun (‖·‖) at hz
  set a : ℝ := 64 / 5 with ha
  set b : ℝ := -48 / 5 with hb
  have : 64 / 5 - 48 / 5 * Complex.I = a + b * Complex.I := by
    rw [ha, hb, sub_eq_add_neg]
    congr
    . norm_num
    rw [← neg_mul]
    congr
    . norm_num
  -- We also have $|z|^4 = |z|\cdot |z|\cdot |z|\cdot |z| = |(z)(z)(z)(z)| = |z^4|$,
  conv at hz =>
    congr
    . rw [norm_pow]
    rw [this, Complex.norm_eq_abs, Complex.abs_add_mul_I, ha, hb]
  -- so $|z^4| = 16$ means that $|z|^4 = 16$,
  norm_num at hz
  rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
    show (16 : ℝ) = 2 ^ 4 by norm_num, pow_left_inj (by positivity) (by norm_num) (by norm_num)] at hz
  -- which gives us $|z| = 16^{\frac{1}{4}} = \boxed{2}$.
  exact hz
