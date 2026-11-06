import Mathlib

/- 22nd Swedish 1982 Problem 2 Show that abc ≥ (a+b-c)(b+c-a)(c+a-b) for positive reals a, b, c. -/
theorem inequalities_147164 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b * c ≥ (a + b - c) * (b + c - a) * (c + a - b) := by
    -- Matlib does have a more general version of the AM-GM inequality, but it's quite cumbersome
    -- to use in the simple case that we need it for
    have h_am_gm {x y: ℝ} (hx: x ≥ 0) (hy: y ≥ 0): (x + y)^2 ≥ 4 * x * y := by calc
      (x + y)^2 = (x - y)^2 + 4 * x * y := by ring
      _ ≥ 4 * x * y := by nlinarith
    -- The lhs of the inequality is always positive
    have h_abc: a * b * c > 0 := by positivity
    -- If x = a + b - c ≤ 0, then the RHS is non-positive, so the inequality is true
    by_cases hx: a + b - c ≤ 0
    have hy: b + c - a ≥ 0 := by linarith
    have hz: c + a - b ≥ 0 := by linarith
    have h_xyz := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hx hy) hz
    linarith
    apply le_of_not_ge at hx
    -- Similarly, if y = b + c - a ≤ 0, then the RHS is non-positive, while the LHS is positive
    by_cases hy: b + c - a ≤ 0
    have hz: c + a - b ≥ 0 := by linarith
    have h_xyz := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hx hy) hz
    linarith
    apply le_of_not_ge at hy
    -- Similarly, if z = c + a - b ≤ 0, then the RHS is again non-positive
    by_cases hz: c + a - b ≤ 0
    have h_xyz := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hx hy) hz
    linarith
    apply le_of_not_ge at hz
    -- We apply AM-GM to the non-negative numbers (x = a + b - c) and (y = b + c - a) to obtain x + y ≥ 2√(xy), so (x + y)^2 ≥ 4xy
    have h_xy := h_am_gm hx hy
    -- We apply AM-GM to the non-negative numbers (y = b + c - a) and (z = c + a - b) to obtain (y + z)^2 ≥ 4yz
    have h_yz := h_am_gm hy hz
    -- We apply AM-GM to the non-negative numbers (z = c + a - b) and (x = a + b - c) to obtain (z + x)^2 ≥ 4zx
    have h_zx := h_am_gm hz hx
    rw [show a + b - c + (b + c - a) = 2*b from by ring] at h_xy
    rw [show b + c - a + (c + a - b) = 2*c from by ring] at h_yz
    rw [show c + a - b + (a + b - c) = 2*a from by ring] at h_zx
    -- Multiplying these inequalities together gives us ((x + y)(y + z)(z + x))^2 ≥ 64x^2 y^2 z^2
    have h_xyyz := mul_le_mul_of_nonneg h_xy h_yz (by positivity) (by positivity)
    have h_xxyyzz := mul_le_mul_of_nonneg h_xyyz h_zx (by positivity) (by positivity)
    -- And so (x + y)(y + z)(z + x) ≥ 8xyz
    apply (sq_le_sq₀ _ _).mp
    calc
      (a * b * c)^2 = 1/64 * (2 * a)^2 * (2 * b)^2 * (2 * c)^2 := by ring
      _ ≥ 1/64 * (4 * (c + a - b) * (a + b - c)) * (4 * (b + c - a) * (c + a - b)) * (4 * (a + b - c) * (b + c - a)) := by linarith
      _ = ((a + b - c) * (b + c - a) * (c + a - b))^2 := by ring
    all_goals positivity