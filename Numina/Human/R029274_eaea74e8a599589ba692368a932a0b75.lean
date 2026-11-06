import Mathlib

open scoped Real

/- 3. If $z \in \mathbf{C}, \arg \left(z^{2}-4\right)=\frac{5 \pi}{6}, \arg \left(z^{2}+4\right)=\frac{\pi}{3}$, then the value of $z$ is -/
theorem algebra_186075 {z : ℂ} (hz : Complex.arg (z ^ 2 - 4) = 5 * Real.pi / 6 ∧ Complex.arg (z ^ 2 + 4) = Real.pi / 3) :
    z = -(1 + √3 * .I) ∨ z = 1 + √3 * .I := by
  -- Let a = ‖z^2 - 4‖ and b = ‖z^2 + 4‖
  set a := ‖z ^ 2 - 4‖ with a_eq
  set b := ‖z ^ 2 + 4‖ with b_eq
  -- Show that (1 / 2) * b + (√3 / 2) * a = 8.
  have eq1 : (1 / 2) * b + (√3 / 2) * a = 8 := calc
    -- We have 8 = ((z ^ 2 + 4) - (z ^ 2 - 4)).re
    --           = (z ^ 2 + 4).re - (z ^ 2 - 4).re
    --           = b * cos ((z ^ 2 + 4).arg) - a * cos ((z ^ 2 - 4).arg)
    --           = b * cos (π / 3) - a * cos (5 π / 6)
    --           = (1 / 2) * b + (√3 / 2) * a.
    (1 / 2) * b + (√3 / 2) * a = (z ^ 2 + 4).re - (z ^ 2 - 4).re := by
        simp_rw [← Complex.abs_mul_cos_arg, ← Complex.norm_eq_abs, ← a_eq, ← b_eq]
        rw [hz.1, hz.2, Real.cos_pi_div_three]
        rw [show 5 * π / 6 = π - π / 6 by linarith, Real.cos_pi_sub, Real.cos_pi_div_six]
        ring
    _ = 8 := by simp; norm_num
  -- Show that (√3 / 2) * b - (1 / 2) * a = 0.
  have eq2 : (√3 / 2) * b - (1 / 2) * a = 0 := calc
    -- We have 0 = ((z ^ 2 + 4) - (z ^ 2 - 4)).im
    --           = (z ^ 2 + 4).im - (z ^ 2 - 4).im
    --           = b * sin ((z ^ 2 + 4).arg) - a * sin ((z ^ 2 - 4).arg)
    --           = b * sin (π / 3) - a * sin (5 π / 6)
    --           = (√3 / 2) * b - (1 / 2) * a.
    (√3 / 2) * b - (1 / 2) * a = (z ^ 2 + 4).im - (z ^ 2 - 4).im := by
        simp_rw [← Complex.abs_mul_sin_arg, ← Complex.norm_eq_abs, ← a_eq, ← b_eq]
        rw [hz.1, hz.2, Real.sin_pi_div_three]
        rw [show 5 * π / 6 = π - π / 6 by linarith, Real.sin_pi_sub, Real.sin_pi_div_six]
        ring
    _ = 0 := by simp
  -- We derive that b = 4.
  have hb : b = 4 := calc
    -- b = (2 * b) / 2
    --   = ((1 / 2 * b + (√3 / 2) * a) + √3 * (√3 / 2 * b - (1 / 2) * a)) / 2
    --   = (8 + √3 * 0) / 2 = 8 / 2 = 4.
    b = (2 * b) / 2 := by ring
    _ = ((1 / 2 * b + (√3 / 2) * a) + √3 * (√3 / 2 * b - (1 / 2) * a)) / 2 := by
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        ring
    _ = (8 + √3 * 0) / 2 := by rw [eq1, eq2]
    _ = 4 := by norm_num
  -- Show that z ^ 2 = -2 + 2√3 * I.
  have hz2 : z ^ 2 = -2 + 2 * √3 * .I := calc
    -- z ^ 2 = (z ^ 2 + 4) - 4
    --       = b * (cos (π / 3) + sin (π / 3) * I) - 4
    --       = 4 * (1 / 2 + √3 / 2 * I) - 4
    --       = -2 + 2√3 * I.
    z ^ 2 = z ^ 2 + 4 - 4 := by simp
    _ = (z ^ 2 + 4).re + (z ^ 2 + 4).im * .I - 4 := by
        rw [Complex.re_add_im]
    _ = b * (1 / 2) + b * (√3 / 2) * .I - 4 := by
        rw [← Complex.abs_mul_cos_arg, ← Complex.norm_eq_abs, ← b_eq, hz.2, Real.cos_pi_div_three]
        rw [← Complex.abs_mul_sin_arg, ← Complex.norm_eq_abs, ← b_eq, hz.2, Real.sin_pi_div_three]
        simp
    _ = -2 + 2 * √3 * .I := by
        simp [hb]
        ring
  -- z is a root of X^2 - (-2 + 2√3 * I) = 0.
  have hz : z ∈ Polynomial.nthRoots 2 (-2 + 2 * √3 * Complex.I) := by
    rw [Polynomial.mem_nthRoots zero_lt_two, hz2]
  -- Show that roots of X^2 - (-2 + 2√3 * I) are -(1 + √3 * I) and 1 + √3 * I.
  have hz_eq : Polynomial.nthRoots 2 (-2 + 2 * √3 * Complex.I) = {-(1 + √3 * Complex.I), 1 + √3 * Complex.I} := by
    -- We have (1 + √3 * I)^2 = -2 + 2√3 * I.
    have ha : (1 + √3 * Complex.I) ^ 2 = -2 + 2 * √3 * Complex.I := by
      ring_nf
      rw [Complex.I_sq, show (√3 : Complex) ^ 2 = (√3 ^ 2 : ℝ) by push_cast; simp]
      rw [Real.sq_sqrt (by norm_num)]
      push_cast
      ring
    -- All roots of X^2 - (-2 + 2√3 * I) are
    -- e^(2 * π * I / 2 * n) * (1 + √3 * I) for n = 0, 1.
    rw [IsPrimitiveRoot.nthRoots_eq (Complex.isPrimitiveRoot_exp 2 (by norm_num)) ha]
    simp
    ring_nf
    simp
    ring
  simpa [hz_eq] using hz