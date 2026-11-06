import Mathlib

/-Simplify the fraction by rationalizing the denominator: $$\frac{4}{\sqrt{108}+2\sqrt{12}+2\sqrt{27}}.$$-/
theorem algebra_13324 : 4 / (Real.sqrt 108 + 2 * Real.sqrt 12 + 2 * Real.sqrt 27) = Real.sqrt 3 / 12 := by
  -- First, we can write $\sqrt{108}=6\sqrt{3}$
  have sqrt108 : √108 = 6 * √3 := by
    have : (108 : ℝ) = 6^2 * 3 := by linarith
    rw [this, Real.sqrt_mul, Real.sqrt_sq]
    repeat positivity
  -- $2\sqrt{12}=4\sqrt{3}$
  have _2sqrt12 : 2 * √12 = 4 * √3 := by
    have : (12 : ℝ) = 2^2 * 3 := by linarith
    rw [this, Real.sqrt_mul, Real.sqrt_sq]
    repeat linarith
  -- and $2\sqrt{27}=6\sqrt{3}$.
  have _2sqrt27 : 2 * √27 = 6 * √3 := by
    have : (27 : ℝ) = 3^2 * 3 := by linarith
    rw [this, Real.sqrt_mul, Real.sqrt_sq]
    repeat linarith
  rw [sqrt108, _2sqrt12, _2sqrt27]

  -- Substituting these, the expression becomes: $$\frac{4}{6\sqrt{3}+4\sqrt{3}+6\sqrt3}=\frac{4}{16\sqrt{3}}=\frac{1}{4\sqrt{3}}=\boxed{\frac{\sqrt{3}}{12}}$$
  calc
    _ = 4 / (16 * √3) := by ring_nf
    _ = 1 / (4 * √3) := by ring_nf
    _ = 1 * √3 / √3 / (4 * √3) := by
      rw [←mul_div, div_self, mul_one]
      positivity
    _ = √3 / (4 * √3 * √3) := by ring_nf
    _ = √3 / 12 := by
      rw [mul_assoc, ←pow_two, Real.sq_sqrt]
      ring_nf
      positivity
