import Mathlib

theorem inequalities_244080 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^3 + b^3 + c^3 = 3) :
    1 ≤ 1 / (a^2 + a + 1) + 1 / (b^2 + b + 1) + 1 / (c^2 + c + 1) := by

  have h1 : 1 / (a^2 + a + 1) ≥ (2 - a) / 3 := by
    have h11 : 0 < (a^2 + a + 1 : ℝ) := by 
      nlinarith [sq_nonneg (a + 1 / 2)]
    apply (le_div_iff₀ h11).mpr
    have h10 : (a - 1)^2 * (a + 1) ≥ 0 := by
      have h4 : (a - 1)^2 ≥ 0 := sq_nonneg (a - 1)
      have h5 : (a + 1) > 0 := by linarith
      nlinarith
    nlinarith

  have h2 : 1 / (b^2 + b + 1) ≥ (2 - b) / 3 := by
    have h11 : 0 < (b^2 + b + 1 : ℝ) := by 
      nlinarith [sq_nonneg (b + 1 / 2)]
    apply (le_div_iff₀ h11).mpr
    have h10 : (b - 1)^2 * (b + 1) ≥ 0 := by
      have h4 : (b - 1)^2 ≥ 0 := sq_nonneg (b - 1)
      have h5 : (b + 1) > 0 := by linarith
      nlinarith
    nlinarith

  have h3 : 1 / (c^2 + c + 1) ≥ (2 - c) / 3 := by
    have h11 : 0 < (c^2 + c + 1 : ℝ) := by 
      nlinarith [sq_nonneg (c + 1 / 2)]
    apply (le_div_iff₀ h11).mpr
    have h10 : (c - 1)^2 * (c + 1) ≥ 0 := by
      have h4 : (c - 1)^2 ≥ 0 := sq_nonneg (c - 1)
      have h5 : (c + 1) > 0 := by linarith
      nlinarith
    nlinarith

  have h5 : a + b + c ≤ 3 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]

  linarith [h1, h2, h3, h5]