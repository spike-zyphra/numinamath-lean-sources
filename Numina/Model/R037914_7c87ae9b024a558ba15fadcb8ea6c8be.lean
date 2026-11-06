import Mathlib

theorem inequalities_60652 (a b c : ℝ) (h : ∀ x ∈ Set.Icc (-1) 1, |a * x ^ 2 + b * x + c| ≤ 1) :
    ∀ x ∈ Set.Icc (-1) 1, |c * x ^ 2 + b * x + a| ≤ 2 := by
  intro x hx
  have h1 : -1 ≤ x := by
    have h1 : x ∈ Set.Icc (-1) 1 := hx
    simp at h1 ⊢
    linarith
  have h2 : x ≤ 1 := by
    have h2 : x ∈ Set.Icc (-1) 1 := hx
    simp at h2 ⊢
    linarith
  have h1_neg1 := h (-1) (by norm_num)
  have h1_0 := h 0 (by norm_num)
  have h1_1 := h 1 (by norm_num)
  -- By abs_le.mp, x ∈ (-1, 1), what about in h3
  have h3 := h x (by exact hx)
  -- |y| <= 1 means -1 <= y <= 1
  have h4 : -1 ≤ a * x ^ 2 + b * x + c := by 
    cases' abs_le.mp h3 with h5 h6
    linarith
  have h5 : a * x ^ 2 + b * x + c ≤ 1 := by
    cases' abs_le.mp h3 with h5 h6
    linarith
  -- For |c * x^2 + b * x + a| <= 2, write it in the form of -2 <= ... <= 2
  rw [abs_le]
  constructor
  · -- Show -2 ≤ c * x ^ 2 + b * x + a
    have h6 : -2 ≤ c * x ^ 2 + b * x + a := by
      norm_num [abs_le] at h1_neg1 h1_0 h1_1
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), 
        sq_nonneg (x), sq_nonneg (x - 0), 
        mul_nonneg (show (0 : ℝ) ≤ 1 - x by nlinarith) (show (0 : ℝ) ≤ x + 1 by nlinarith)
      ]
    linarith
  · -- Show c * x ^ 2 + b * x + a ≤ 2
    have h7 : c * x ^ 2 + b * x + a ≤ 2 := by 
      norm_num [abs_le] at h1_neg1 h1_0 h1_1
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), 
        sq_nonneg (x), sq_nonneg (x - 0), 
        mul_nonneg (show (0 : ℝ) ≤ 1 - x by nlinarith) (show (0 : ℝ) ≤ x + 1 by nlinarith)
      ]
    linarith