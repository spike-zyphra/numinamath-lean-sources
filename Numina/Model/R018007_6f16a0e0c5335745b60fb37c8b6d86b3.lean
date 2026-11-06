import Mathlib

theorem inequalities_180367 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.sqrt x / (y ^ 6 * Real.sqrt y) + Real.sqrt y / (x ^ 6 * Real.sqrt x) ≥
    1 / x ^ 6 + 1 / y ^ 6 := by
  have h1 : 0 < x := hx
  have h2 : 0 < y := hy
  have hx1 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hy1 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have h3 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)
  have h4 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith)
  have h5 : x ^ 6 > 0 := by positivity
  have h6 : y ^ 6 > 0 := by positivity

  have h7 : Real.sqrt x / (y ^ 6 * Real.sqrt y) + Real.sqrt y / (x ^ 6 * Real.sqrt x) - (1 / x ^ 6 + 1 / y ^ 6) ≥ 0 := by
    have h8 : Real.sqrt x / (y ^ 6 * Real.sqrt y) - 1 / y ^ 6 ≥ (1 / x ^ 6 - Real.sqrt y / (x ^ 6 * Real.sqrt x)) := by
      have h8 : Real.sqrt x / (y ^ 6 * Real.sqrt y) - 1 / y ^ 6 = (Real.sqrt x - Real.sqrt y) / (y ^ 6 * Real.sqrt y) := by
        field_simp
        <;> nlinarith [Real.sqrt_pos.2 hx, Real.sqrt_pos.2 hy, h3, h4]
      have h9 : (1 / x ^ 6 - Real.sqrt y / (x ^ 6 * Real.sqrt x)) = (Real.sqrt x - Real.sqrt y) / (x ^ 6 * Real.sqrt x) := by
        field_simp
        <;> nlinarith [Real.sqrt_pos.2 hx, Real.sqrt_pos.2 hy, h3, h4]
      rw [h8, h9]
      by_cases h10 : Real.sqrt x ≥ Real.sqrt y
      · -- Assume sqrt x >= sqrt y
        have h11 : Real.sqrt x - Real.sqrt y ≥ 0 := by linarith
        have h12 : x ≥ y := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), Real.sqrt_nonneg x, Real.sqrt_nonneg y, h10]
        have h13 : x ^ 6 * Real.sqrt x ≥ y ^ 6 * Real.sqrt y := by
          have h14 : x ≥ y := h12
          have h15 : Real.sqrt x ≥ Real.sqrt y := h10
          have h16 : x ^ 6 ≥ y ^ 6 := by
            apply pow_le_pow_left
            all_goals linarith
          have h17 : Real.sqrt x ≥ Real.sqrt y := h10
          nlinarith [h14, h16, h17, Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith)]
        have h18 : (Real.sqrt x - Real.sqrt y) / (y ^ 6 * Real.sqrt y) ≥ (Real.sqrt x - Real.sqrt y) / (x ^ 6 * Real.sqrt x) := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith [Real.sqrt_nonneg y, Real.sqrt_nonneg x, h11, h13, Real.sqrt_nonneg y, Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
        linarith
      · -- Assume sqrt y > sqrt x
        have h14 : Real.sqrt y > Real.sqrt x := by
          by_contra h
          push_neg at h
          have : Real.sqrt y < Real.sqrt x := by linarith
          linarith
        have h11 : Real.sqrt x - Real.sqrt y ≤ 0 := by linarith
        have h12 : x ≤ y := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), Real.sqrt_nonneg x, Real.sqrt_nonneg y, show Real.sqrt y ≥ Real.sqrt x by linarith [h14]]
        have h13 : x ^ 6 * Real.sqrt x ≤ y ^ 6 * Real.sqrt y := by
          have h14 : x ≤ y := h12
          have h15 : Real.sqrt x ≤ Real.sqrt y := by
            nlinarith [h14, Real.sqrt_nonneg x, Real.sqrt_nonneg y]
          have h16 : x ^ 6 ≤ y ^ 6 := by
            apply pow_le_pow_left
            all_goals linarith
          have h17 : Real.sqrt x ≤ Real.sqrt y := by
            nlinarith [h14, Real.sqrt_nonneg x, Real.sqrt_nonneg y]
          nlinarith [h14, h16, h17, Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith)]
        have h18 : (Real.sqrt x - Real.sqrt y) / (y ^ 6 * Real.sqrt y) ≥ (Real.sqrt x - Real.sqrt y) / (x ^ 6 * Real.sqrt x) := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith [Real.sqrt_nonneg y, Real.sqrt_nonneg x, h11, h13, Real.sqrt_nonneg y, Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
        linarith
    linarith
  linarith [h7]