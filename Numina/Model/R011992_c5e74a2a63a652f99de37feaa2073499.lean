import Mathlib

theorem algebra_170282 (m : ℝ) (h : ∀ x, 4*x^2 - (3*m+1)*x - m - 2 = 0 → -1 < x ∧ x < 2) :
    m ∈ Set.Ioo (-3/2) (12/7) := by
  have eq1 := h ((3 * m + 1 + Real.sqrt ((3 * m + 1) ^ 2 + 16 * (m + 2))) / 8)
    (by
      nlinarith [Real.sqrt_nonneg ((3 * m + 1) ^ 2 + 16 * (m + 2)), Real.sq_sqrt (show ((3 * m + 1) ^ 2 + 16 * (m + 2)) ≥ 0 by nlinarith)]
    )
  have h1 : -1 < (3 * m + 1 + Real.sqrt ((3 * m + 1) ^ 2 + 16 * (m + 2))) / 8 := eq1.1
  have h2 : (3 * m + 1 + Real.sqrt ((3 * m + 1) ^ 2 + 16 * (m + 2))) / 8 < 2 := eq1.2
  have eq2 := h ((3 * m + 1 - Real.sqrt ((3 * m + 1) ^ 2 + 16 * (m + 2))) / 8)
    (by 
      nlinarith [Real.sqrt_nonneg ((3 * m + 1) ^ 2 + 16 * (m + 2)), Real.sq_sqrt (show ((3 * m + 1) ^ 2 + 16 * (m + 2)) ≥ 0 by nlinarith)]
    )
  have h3 : -1 < (3 * m + 1 - Real.sqrt ((3 * m + 1) ^ 2 + 16 * (m + 2))) / 8 := eq2.1
  have h4 : (3 * m + 1 - Real.sqrt ((3 * m + 1) ^ 2 + 16 * (m + 2))) / 8 < 2 := eq2.2
  have lower : -3 / 2 < m := by 
    by_contra h6 
    push_neg at h6 
    nlinarith [Real.sqrt_nonneg ((3 * m + 1) ^ 2 + 16 * (m + 2)), 
      Real.sq_sqrt (show ((3 * m + 1) ^ 2 + 16 * (m + 2)) ≥ 0 by nlinarith), 
      sq_nonneg (m + 3 / 2), sq_nonneg (m - 12 / 7)
    ]
  have upper : m < 12 / 7 := by 
    by_contra h7 
    push_neg at h7 
    nlinarith [Real.sqrt_nonneg ((3 * m + 1) ^ 2 + 16 * (m + 2)), 
      Real.sq_sqrt (show ((3 * m + 1) ^ 2 + 16 * (m + 2)) ≥ 0 by nlinarith), 
      sq_nonneg (m + 3 / 2), sq_nonneg (m - 12 / 7)
    ]
  exact ⟨by linarith, by linarith⟩