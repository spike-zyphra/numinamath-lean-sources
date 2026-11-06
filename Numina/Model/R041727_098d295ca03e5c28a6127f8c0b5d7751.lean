import Mathlib

theorem inequalities_112888 (a b c : ℝ) (h : ∀ x ∈ Set.Icc (-1) 1, abs (a * x^2 + b * x + c) ≤ 1) :
    ∀ x ∈ Set.Icc (-1) 1, abs (c * x^2 + b * x + a) ≤ 2 := by
  have h1 := h (-1) (by norm_num)
  have h2 := h 0 (by norm_num)
  have h3 := h 1 (by norm_num)

  have h1' : -1 ≤ a - b + c := by
    norm_num at h1 ⊢
    linarith [abs_le.mp h1]

  have h1'' : a - b + c ≤ 1 := by
    norm_num at h1 ⊢
    linarith [abs_le.mp h1]

  have h2' : -1 ≤ c := by
    norm_num at h2 ⊢
    linarith [abs_le.mp h2]

  have h2'' : c ≤ 1 := by
    norm_num at h2 ⊢
    linarith [abs_le.mp h2]

  have h3' : -1 ≤ a + b + c := by
    norm_num at h3 ⊢
    linarith [abs_le.mp h3]

  have h3'' : a + b + c ≤ 1 := by
    norm_num at h3 ⊢
    linarith [abs_le.mp h3]

  intro x hx
  have hx1 : -1 ≤ x := by
    have h : x ∈ Set.Icc (-1) 1 := hx
    exact h.1

  have hx2 : x ≤ 1 := by
    have h : x ∈ Set.Icc (-1) 1 := hx
    exact h.2

  have h4 : x ^ 2 ≤ 1 := by
    nlinarith

  have h5 : -2 ≤ c * x^2 + b * x + a := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]

  have h6 : c * x^2 + b * x + a ≤ 2 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
  
  apply abs_le.mpr
  constructor <;> nlinarith