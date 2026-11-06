import Mathlib

theorem algebra_255194 (a b c : ℝ) (h : ∀ x ∈ Set.Icc (-1) 1, |a * x ^ 2 + b * x + c| ≤ 1)
    (h' : ∃ x ∈ Set.Icc (-1) 1, |a * x ^ 2 + b * x + c| = 1) :
    ∀ x ∈ Set.Icc (-1) 1, |c * x ^ 2 + b * x + a| ≤ 2 := by
  intro x hx
  have h1 : -1 ≤ x := by
    have h1 : x ∈ Set.Icc (-1) 1 := hx
    simp at h1 ⊢
    linarith
  have h2 : x ≤ 1 := by
    have h1 : x ∈ Set.Icc (-1) 1 := hx
    simp at h1 ⊢
    linarith
  have h3 := h (-1) (by norm_num)
  have h4 := h 0 (by norm_num)
  have h5 := h 1 (by norm_num)
  have h6 : -1 ≤ a - b + c := by 
    linarith [abs_le.mp h3]
  have h7 : a - b + c ≤ 1 := by 
    linarith [abs_le.mp h3]
  have h8 : -1 ≤ c := by
    linarith [abs_le.mp h4]
  have h9 : c ≤ 1 := by
    linarith [abs_le.mp h4]
  have h10 : -1 ≤ a + b + c := by
    linarith [abs_le.mp h5]
  have h11 : a + b + c ≤ 1 := by
    linarith [abs_le.mp h5]
  have h16 : -1 ≤ x ^ 2 := by
    nlinarith
  have h17 : x ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (x)]
  have h18 : -2 ≤ c * x ^ 2 + b * x + a := by
    nlinarith [sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 1)]
  have h19 : c * x ^ 2 + b * x + a ≤ 2 := by
    nlinarith [sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 1)]
  apply abs_le.mpr
  constructor
  · linarith
  · linarith