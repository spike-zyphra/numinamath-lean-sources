import Mathlib

theorem algebra_281583 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 / y + y^2 / z + z^2 / x = x^2 / z + z^2 / y + y^2 / x) :
    x = y ∨ y = z ∨ x = z
  := by
  have h1 : x^2 / y + y^2 / z + z^2 / x - (x^2 / z + z^2 / y + y^2 / x) = 0 := by linarith
  have h2 : x^3 * (z - y) + y^3 * (x - z) + z^3 * (y - x) = 0 := by
    have h3 : x^2 / y + y^2 / z + z^2 / x - (x^2 / z + z^2 / y + y^2 / x) = 0 := h1
    have hxyz1 : x ≠ 0 := by linarith
    have hxyz2 : y ≠ 0 := by linarith
    have hxyz3 : z ≠ 0 := by linarith
    have h4 : x^3 * (z - y) + y^3 * (x - z) + z^3 * (y - x) = 0 := by 
      have h5 : x^3 * (z - y) + y^3 * (x - z) + z^3 * (y - x) = 
        (x * y * z) * (x^2 / y + y^2 / z + z^2 / x - (x^2 / z + z^2 / y + y^2 / x)) := by 
        field_simp
        ring
      rw [h5]
      have eq4 : (x^2 / y + y^2 / z + z^2 / x - (x^2 / z + z^2 / y + y^2 / x)) = 0 := h3
      rw [eq4]
      all_goals linarith
    exact_mod_cast h4
  have h4 : (x - y) * (y - z) * (z - x) * (x + y + z) = 0 := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
    ]
  have hxyz1 : x + y + z > 0 := by linarith
  by_cases h9 : x + y + z ≠ 0
  · 
    have h5 : (x - y) * (y - z) * (z - x) = 0 := by 
      apply (mul_right_inj' h9).mp 
      linarith 
    cases' (mul_eq_zero.mp h5) with h6 h7
    cases' (mul_eq_zero.mp h6) with h8 h9
    · 
      left
      linarith 
    · 
      right
      left
      linarith 
    · 
      right
      right
      linarith 
  · 
    have h10 : x + y + z = 0 := by 
      by_contra h_eq
      push_neg at h_eq
      exfalso 
      apply h9 
      linarith 
    linarith