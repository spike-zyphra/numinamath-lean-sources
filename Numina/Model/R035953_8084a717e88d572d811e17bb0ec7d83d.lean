import Mathlib

theorem algebra_598992 (x y z r : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hr : 0 < r)
    (h1 : z * Real.sqrt (x^2 - r^2) = x^2) (h2 : x * y = r * z) : x^2 + y^2 = z^2 := by
  have h3 : x ^ 2 ≥ r ^ 2 := by
    by_contra h
    push_neg at h
    have h4 : Real.sqrt (x^2 - r^2) = 0 := by
      rw [Real.sqrt_eq_zero']
      nlinarith
      all_goals nlinarith
    have h5 : z * 0 = x^2 := by 
      rw [h4] at h1
      all_goals nlinarith
    have h6 : x^2 = 0 := by nlinarith
    have h7 : x = 0 := by
      nlinarith
    linarith
  have h4 : Real.sqrt (x ^ 2 - r ^ 2) ^ 2 = x ^ 2 - r ^ 2 := by
    apply Real.sq_sqrt
    nlinarith
  have h5 : z^2 * (x^2 - r^2) = x^4 := by
    have eq1 : z * Real.sqrt (x^2 - r^2) = x^2 := h1
    calc
      z^2 * (x^2 - r^2) = (z * Real.sqrt (x^2 - r^2)) ^ 2 := by
        have h55 : Real.sqrt (x ^ 2 - r ^ 2) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - r ^ 2)
        nlinarith [Real.sqrt_nonneg (x ^ 2 - r ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - r ^ 2 by nlinarith)]
      _ = (x^2) ^ 2 := by
        rw [show z * Real.sqrt (x^2 - r^2) = x^2 by linarith [h1]]
      _ = x^4 := by
        ring
  have h6 : r = (x * y) / z := by
    have h61 : z > 0 := hz
    field_simp
    nlinarith
  rw [h6] at h5
  -- Now h5 is: z ^ 2 * (x ^ 2 - (x * y / z) ^ 2) = x ^ 4
  have h7 : z^2 * (x^2 - (x * y / z)^2) = x^4 := h5
  have h8 : z^2 * x^2 - (x * y) ^ 2 = x^4 := by
    field_simp [hz.ne.symm] at h7 ⊢
    ring_nf at h7 ⊢
    linarith [h7]
  have h9 : z^2 - y^2 = x^2 := by
    have h81 : x ^ 2 > 0 := by nlinarith
    apply (mul_left_inj' (show x ^ 2 ≠ 0 by nlinarith)).mp
    linarith [h8]
  nlinarith