import Mathlib

/- Let $x$, $y$, and $z$ be real numbers such that
\[\cos x + \cos y + \cos z = \sin x + \sin y + \sin z = 0.\]Find the sum of all possible values of $\cos (2x - y - z).$-/
theorem calculus_22444 (x y z : ℝ) (hx : Real.cos x + Real.cos y + Real.cos z = 0) (hy : Real.sin x + Real.sin y + Real.sin z = 0) :
    Real.cos (2 * x - y - z) = 1 := by
  have heix := Complex.exp_mul_I x
  have heiy := Complex.exp_mul_I y
  have heiz := Complex.exp_mul_I z
  -- Let $a = e^{ix}$, $b = e^{iy}$, and $c = e^{iz}$.
  set a : ℂ := Complex.exp (x * .I) with ha
  set b : ℂ := Complex.exp (y * .I) with hb
  set c : ℂ := Complex.exp (z * .I) with hc
  have ha_ne_zero : a ≠ 0 := Complex.exp_ne_zero _
  have hb_ne_zero : b ≠ 0 := Complex.exp_ne_zero _
  have hc_ne_zero : c ≠ 0 := Complex.exp_ne_zero _
  --   Then
  -- \begin{align*}
  -- a + b + c &= e^{ix} + e^{iy} + e^{iz} \\
  -- &= (\cos x + \cos y + \cos z) + i (\sin x + \sin y + \sin z) \\
  -- &= 0.
  -- \end{align*}
  have sum_abc : a + b + c = 0 := by
    apply Complex.ext
    all_goals simpa [ha, hb, hc]
  replace sum_abc : a = - b - c := by linear_combination sum_abc
  --   Also,
  -- \begin{align*}
  -- \frac{1}{a} + \frac{1}{b} + \frac{1}{c} &= \frac{1}{e^{ix}} + \frac{1}{e^{iy}} + \frac{1}{e^{iz}} \\
  -- &= e^{-ix} + e^{-iy} + e^{-iz} \\
  -- &= [\cos (-x) + \cos (-y) + \cos (-z)] + i [\sin (-x) + \sin (-y) + \sin (-z)] \\
  -- &= (\cos x + \cos y + \cos z) - i (\sin x + \sin y + \sin z) \\
  -- &= 0.
  -- \end{align*}
  have sum_abc_inv : a⁻¹ + b⁻¹ + c⁻¹ = 0 := by
    rw [ha, hb, hc]
    repeat rw [← Complex.exp_neg, ← neg_mul, ← Complex.ofReal_neg, Complex.exp_mul_I]
    apply Complex.ext
    . simp
      norm_cast
    simp
    norm_cast
    linear_combination -hy
  --   Hence,
  -- \[abc \left( \frac{1}{a} + \frac{1}{b} + \frac{1}{c} \right) = ab + ac + bc = 0.\]Note that $\cos (2x - y - z)$ is the real part of $e^{i (2 \alpha - \beta - \gamma)},$ and
  -- \begin{align*}
  -- e^{i (2 \alpha - \beta - \gamma)} &= \frac{a^2}{bc} \\
  -- &= \frac{a \cdot a}{-ab - ac} \\
  -- &= \frac{a (-b - c)}{-ab - ac} \\
  -- &= 1.
  -- \end{align*}
  have h : a * b + b * c + c * a = 0 := by
    have : (a * b * c) * (a⁻¹ + b⁻¹ + c⁻¹) = 0 := by norm_num [sum_abc_inv]
    convert this using 1
    field_simp
    ring
  have h : b * c = - a * b - a * c := by linear_combination h
  -- Therefore, $\cos (2x - y - z) = \boxed{1}.$
  have heiw := Complex.exp_mul_I (2 * x - y - z)
  set d : ℂ := Complex.exp ((2 * x - y - z) * .I) with hd
  have : d = 1 := by
    rw [hd, sub_mul, sub_mul, Complex.exp_sub, Complex.exp_sub, mul_assoc]
    have : Complex.exp (2 * (x * Complex.I)) = (Complex.exp (x * Complex.I)) ^ 2 := by
      rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by rfl, Complex.exp_nat_mul]
    rw [this, ← ha, ← hb, ← hc]
    field_simp
    rw [pow_two]
    nth_rw 1 [sum_abc]
    rw [h]
    ring
  apply_fun Complex.re at this
  convert this
  rw [hd, Complex.exp_mul_I, Real.cos]
  simp
  norm_cast
