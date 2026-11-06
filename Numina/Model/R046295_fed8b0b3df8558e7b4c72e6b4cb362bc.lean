import Mathlib

theorem algebra_143707 (a b c : ℝ) (h : ∀ x ∈ Set.Icc (-1) 1, -1 ≤ a * x^2 + b * x + c ∧ a * x^2 + b * x + c ≤ 1) :
    ∀ x ∈ Set.Icc (-2) 2, -7 ≤ a * x^2 + b * x + c ∧ a * x^2 + b * x + c ≤ 7 := by
  intro x hx
  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  have h3 := h 0 (by norm_num)
  have h4 : -1 ≤ a + b + c := by
    nlinarith
  have h5 : a + b + c ≤ 1 := by
    nlinarith
  have h6 : -1 ≤ a - b + c := by
    nlinarith
  have h7 : a - b + c ≤ 1 := by
    nlinarith
  have h8 : -1 ≤ c := by
    nlinarith
  have h9 : c ≤ 1 := by
    nlinarith
  have h10 : x ≥ -2 := by
    have h10 : x ∈ Set.Icc (-2) 2 := hx
    simp at h10 ⊢
    linarith
  have h11 : x ≤ 2 := by
    have h11 : x ∈ Set.Icc (-2) 2 := hx
    simp at h11 ⊢
    linarith
  have h12 : x ^ 2 ≤ 4 := by nlinarith [sq_nonneg (x), sq_nonneg (x - 2), sq_nonneg (x + 2)]
  have h13 : -7 ≤ a * x ^ 2 + b * x + c := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 4)]
  have h14 : a * x ^ 2 + b * x + c ≤ 7 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 4)]
  constructor
  · linarith
  · linarith