import Mathlib

theorem inequalities_599528 (a b c : ℝ) (ha : a ≥ -3 / 4) (hb : b ≥ -3 / 4) (hc : c ≥ -3 / 4)
    (h : a + b + c = 1) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) ≤ 9 / 10 := by 
  have h1 : a / (a ^ 2 + 1) ≤ (36 / 50) * a + (3 / 50) := by
    have h3 : a ^ 2 + 1 > 0 := by nlinarith
    apply (div_le_iff₀ h3).mpr
    nlinarith [sq_nonneg (a ^ 2 - 1 / 25 : ℝ), sq_nonneg (a + 1 / 4 : ℝ), sq_nonneg (a - 1 / 3 : ℝ),
      sq_nonneg (a ^ 3 - 1 / 3 : ℝ), sq_nonneg (a + 3 / 4 : ℝ),
      sq_nonneg (a ^ 2 - 1 : ℝ), sq_nonneg (a - 1 : ℝ)
      ]

  have h2 : b / (b ^ 2 + 1) ≤ (36 / 50) * b + (3 / 50) := by
    have h5 : b ^ 2 + 1 > 0 := by nlinarith
    apply (div_le_iff₀ h5).mpr
    nlinarith [sq_nonneg (b ^ 2 - 1 / 25 : ℝ), sq_nonneg (b + 1 / 4 : ℝ), sq_nonneg (b - 1 / 3 : ℝ),
      sq_nonneg (b ^ 3 - 1 / 3 : ℝ), sq_nonneg (b + 3 / 4 : ℝ),
      sq_nonneg (b ^ 2 - 1 : ℝ), sq_nonneg (b - 1 : ℝ)
      ]

  have h3 : c / (c ^ 2 + 1) ≤ (36 / 50) * c + (3 / 50) := by
    have h5 : c ^ 2 + 1 > 0 := by nlinarith
    apply (div_le_iff₀ h5).mpr
    nlinarith [sq_nonneg (c ^ 2 - 1 / 25 : ℝ), sq_nonneg (c + 1 / 4 : ℝ), sq_nonneg (c - 1 / 3 : ℝ),
      sq_nonneg (c ^ 3 - 1 / 3 : ℝ), sq_nonneg (c + 3 / 4 : ℝ),
      sq_nonneg (c ^ 2 - 1 : ℝ), sq_nonneg (c - 1 : ℝ)
      ]

  have h4 : a + b + c = 1 := h

  linarith [h1, h2, h3, h4]