import Mathlib

theorem algebra_300160 {a b c : ℝ} (h : ∀ x : ℝ, x^2 - 3 * x - 1 = 0 → x^4 + a * x^2 + b * x + c = 0) :
    a + b - 2 * c = -13 := by
  have eq1 := h ((3 + Real.sqrt 13) / 2) (by
    nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  )
  have eq2 := h ((3 - Real.sqrt 13) / 2) (by
    nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  )
  have h1 : ((3 + Real.sqrt 13) / 2) ^ 4 + a * ((3 + Real.sqrt 13) / 2) ^ 2 + b * ((3 + Real.sqrt 13) / 2) + c = 0 := by
    simpa using eq1
  have h2 : ((3 - Real.sqrt 13) / 2) ^ 4 + a * ((3 - Real.sqrt 13) / 2) ^ 2 + b * ((3 - Real.sqrt 13) / 2) + c = 0 := by
    simpa using eq2
  have h3 : a + b - 2 * c = -13 := by
    have h4 : ((3 + Real.sqrt 13) / 2) ^ 2 = 3 * ((3 + Real.sqrt 13) / 2) + 1 := by
      nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    have h5 : ((3 + Real.sqrt 13) / 2) ^ 4 = 33 * ((3 + Real.sqrt 13) / 2) + 10 := by
      calc
        ((3 + Real.sqrt 13) / 2) ^ 4 = (((3 + Real.sqrt 13) / 2) ^ 2) ^ 2 := by ring
        _ = (3 * ((3 + Real.sqrt 13) / 2) + 1) ^ 2 := by rw [h4]
        _ = 33 * ((3 + Real.sqrt 13) / 2) + 10 := by
          nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    have h6 : ((3 - Real.sqrt 13) / 2) ^ 2 = 3 * ((3 - Real.sqrt 13) / 2) + 1 := by
      nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    have h7 : ((3 - Real.sqrt 13) / 2) ^ 4 = 33 * ((3 - Real.sqrt 13) / 2) + 10 := by
      calc
        ((3 - Real.sqrt 13) / 2) ^ 4 = (((3 - Real.sqrt 13) / 2) ^ 2) ^ 2 := by ring
        _ = (3 * ((3 - Real.sqrt 13) / 2) + 1) ^ 2 := by rw [h6]
        _ = 33 * ((3 - Real.sqrt 13) / 2) + 10 := by
          nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    rw [h5] at h1
    rw [h7] at h2
    -- Simplify a*x^2 and b*x terms using h4, h6 and known x values
    rw [h4] at h1
    rw [h6] at h2
    -- Now h1 and h2 are linear in a, b, c. Let's see what they look like.
    -- They should be (after possible ring_nf):
    -- (33 + 3*a + b)*x + (10 + a + c) = 0 for x = (3 ± √13)/2
    -- Since these equations must hold for these distinct x's, the coefficients must be zero:
    have eq1 : 33 + 3*a + b = 0 := by
      have h9 : (33 + 3*a + b)*((3 + Real.sqrt 13) / 2) + (10 + a + c) = 0 := by
        ring_nf at h1 ⊢
        exact h1
      have h10 : (33 + 3*a + b)*((3 - Real.sqrt 13) / 2) + (10 + a + c) = 0 := by
        ring_nf at h2 ⊢
        exact h2
      have h11 : 33 + 3*a + b = 0 := by
        ring_nf at h9 h10 ⊢
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num : (13 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num : (0 : ℝ) ≤ (13 : ℝ))]
      exact h11
    have eq2 : 10 + a + c = 0 := by
      -- Using previous eq1 in h9
      have h9 : (33 + 3*a + b)*((3 + Real.sqrt 13) / 2) + (10 + a + c) = 0 := by
        ring_nf at h1 ⊢
        exact h1
      rw [show 33 + 3*a + b = 0 by linarith [eq1]] at h9
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num : (13 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num : (0 : ℝ) ≤ (13 : ℝ))]
    -- We have two equations: eq1 and eq2. Let's express them:
    -- eq1: b = -33 - 3*a
    -- eq2: c = -10 - a
    -- Substitute into a + b - 2*c:
    nlinarith [eq1, eq2]
  exact h3