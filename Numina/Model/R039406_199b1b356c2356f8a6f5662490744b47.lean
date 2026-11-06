import Mathlib

theorem inequalities_66606 (a b c : ℝ) (ha : a + b + c > 0)
    (h : ∀ x : ℝ, a * x ^ 2 + b * x + c ≠ 0) : c > 0 := by
  by_contra h1
  push_neg at h1
  have h2 : b ^ 2 - 4 * a * c < 0 := by 
    by_contra h3
    push_neg at h3
    have h3 : b ^ 2 - 4 * a * c ≥ 0 := by nlinarith
    by_cases h4 : a = 0
    · -- if a = 0, then the equation becomes linear
      rw [h4] at h3
      have h5 : b * ( -c / b ) + c = 0 := by
        have hb : b ≠ 0 := by 
          by_contra h6
          have : b = 0 := by linarith
          rw [h4, this] at ha
          nlinarith
        field_simp [hb]
        <;> nlinarith [sq_pos_of_ne_zero hb]
      have h5' : a * (-c / b ) ^ 2 + b * (-c / b ) + c = 0 := by
        rw [h4]
        linarith [h5]
      have h5'' : a * (-c / b ) ^ 2 + b * (-c / b ) + c ≠ 0 := h (-c / b )
      contradiction
    · -- a ≠ 0, can apply quadratic formula
      have h4' : a ≠ 0 := by 
        intro ha0
        apply h4
        linarith
      have h5 : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
        use (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
        field_simp [h4']
        <;> nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), Real.sq_sqrt (show (b ^ 2 - 4 * a * c) ≥ 0 by linarith ) ]
      rcases h5 with ⟨x, hx⟩
      have hx' : a * x ^ 2 + b * x + c = 0 := by linarith [hx ]
      have hx2 : a * x ^ 2 + b * x + c ≠ 0 := h x
      contradiction
  -- Now we have the discriminant is negative: $b^2 - 4ac < 0$
  -- From $b^2 < 4ac$. Since b² >=0, we need 4ac > b².
  -- From h1: c ≤0
  -- From h2: b^2 -4*a*c < 0
  nlinarith [sq_nonneg (b + 2 * a), sq_nonneg (b - 2 * a), sq_nonneg (a + b + c), sq_nonneg (a), sq_nonneg (c), sq_nonneg (b)]