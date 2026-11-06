import Mathlib

theorem algebra_222837 (a b c : ℝ) (h : ∀ x, |x| ≤ 1 → |a * x^2 + b * x + c| ≤ 1) :
    ∀ x, |x| ≤ 1 → |c * x^2 + b * x + a| ≤ 2 := by
  intro x hx
  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  have h3 := h 0 (by norm_num)
  have h11 : -1 ≤ a + b + c := by 
    linarith [abs_le.mp h1]
  have h12 : a + b + c ≤ 1 := by 
    linarith [abs_le.mp h1]
  have h21 : -1 ≤ a - b + c := by
    linarith [abs_le.mp h2]
  have h22 : a - b + c ≤ 1 := by
    linarith [abs_le.mp h2]
  have h31 : -1 ≤ c := by
    linarith [abs_le.mp h3]
  have h32 : c ≤ 1 := by
    linarith [abs_le.mp h3]
  have h4 : -1 ≤ x := by
    linarith [abs_le.mp hx]
  have h5 : x ≤ 1 := by
    linarith [abs_le.mp hx]
  have h6 : -1 ≤ x^2 := by
    nlinarith [sq_nonneg x]
  have h7 : x^2 ≤ 1 := by
    nlinarith [sq_nonneg x, h4, h5]
  have h8 : -2 ≤ c * x^2 + b * x + a := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, 
      h4, h5, 
      mul_self_nonneg (x - 1), mul_self_nonneg (x + 1), 
      mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ x + 1 by linarith)
    ]
  have h9 : c * x^2 + b * x + a ≤ 2 := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, 
      h4, h5, 
      mul_self_nonneg (x - 1), mul_self_nonneg (x + 1), 
      mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ x + 1 by linarith)
    ]
  apply abs_le.mpr
  constructor <;> linarith [h8, h9]