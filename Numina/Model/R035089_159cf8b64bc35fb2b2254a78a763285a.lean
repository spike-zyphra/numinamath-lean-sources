import Mathlib

theorem inequalities_295589 (k : ℝ) (hk : k > 1) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hac : a ≤ k * c) (hbc : b ≤ k * c)
    (habc : a * b ≤ c ^ 2) : a + b ≤ (k + 1 / k) * c := by
  have h1 : k > 0 := by linarith
  by_cases h2 : c > 0
  · -- c > 0
    have h3 : a / c ≥ 0 := by
      apply div_nonneg
      linarith
      linarith
    have h4 : b / c ≥ 0 := by
      apply div_nonneg
      linarith
      linarith
    have h9 : (a + b) ≤ (k + 1 / k) * c := by
      have h10 : k * (a + b) ≤ c * (k^2 + 1) := by
        nlinarith [sq_nonneg (a - k * c), sq_nonneg (b - k * c), sq_nonneg (a * k - b), sq_nonneg (b * k - a),
          sq_nonneg (a * k * b - c^2 * k), sq_nonneg (c - a / k), sq_nonneg (c - b / k),
          mul_pos (show 0 < k by nlinarith) (show 0 < c by nlinarith), sq_nonneg (a - b), sq_nonneg (a * k - c), sq_nonneg (b * k - c)]
      have h11 : c > 0 := by linarith
      have h12 : k > 0 := by linarith
      have h13 : a + b ≤ (k + 1 / k) * c := by
        have h14 : c > 0 := by linarith
        have h15 : k > 0 := by linarith
        have h16 : k * (a + b) ≤ c * (k^2 + 1) := h10
        have h17 : (k + 1 / k) * c = (c * (k^2 + 1)) / k := by
          field_simp
          <;> nlinarith
        have h18 : k > 0 := by linarith
        have h19 : (k * (a + b)) / k ≤ (c * (k^2 + 1)) / k := by
          apply (div_le_div_right (by positivity)).mpr
          linarith
        have h20 : (k * (a + b)) / k = a + b := by
          field_simp
        have h21 : a + b ≤ (c * (k^2 + 1)) / k := by
          linarith [h20, h19]
        have h22 : (c * (k^2 + 1)) / k = (k + 1 / k) * c := by
          field_simp
          <;> nlinarith
        linarith [h21, h22]
      exact h13
    linarith
  · -- c ≤ 0
    push_neg at h2
    have hc0 : c = 0 := by
      nlinarith [hc, h2]
    -- c = 0, so a and b must be 0
    have ha0 : a = 0 := by
      nlinarith [hac, hc0, ha]
    have hb0 : b = 0 := by
      nlinarith [hbc, hc0, hb]
    -- Conclusion
    rw [ha0, hb0, hc0]
    nlinarith