import Mathlib

theorem inequalities_52143 (a b c : ℝ) (h : ∀ x ∈ Set.Icc (-1) 1, |a * x ^ 2 + b * x + c| ≤ 1) :
    ∀ x ∈ Set.Icc (-1) 1, |c * x ^ 2 + b * x + a| ≤ 2 := by 
  intro x hx
  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  have h3 := h 0 (by norm_num)
  have h11 := abs_le.mp h1
  have h22 := abs_le.mp h2
  have h33 := abs_le.mp h3
  have h10 : -1 ≤ x := by
    have h11 : x ∈ Set.Icc (-1) 1 := hx
    exact h11.1
  have h11 : x ≤ 1 := by
    have h11 : x ∈ Set.Icc (-1) 1 := hx
    exact h11.2
  have h12 : x ^ 2 ≤ 1 := by
    nlinarith
  have h13 : -2 ≤ c * x ^ 2 + b * x + a := by 
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, 
      sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x), 
      mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ 1 + x by linarith)
    ]
  have h14 : c * x ^ 2 + b * x + a ≤ 2 := by 
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, 
      sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x), 
      mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ 1 + x by linarith)
    ]
  apply abs_le.mpr 
  constructor <;> nlinarith