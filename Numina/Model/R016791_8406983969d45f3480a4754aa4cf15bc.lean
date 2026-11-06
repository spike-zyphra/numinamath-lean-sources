import Mathlib

theorem algebra_159171 (x y : ℝ) (h : x^2 + 2 * Real.cos y = 1) :
    x - Real.cos y ∈ Set.Icc (-1) (Real.sqrt 3 + 1) := by
  have h1 : Real.cos y = (1 - x^2) / 2 := by
    nlinarith
  have h2 : -1 ≤ Real.cos y := Real.neg_one_le_cos y
  have h3 : Real.cos y ≤ 1 := Real.cos_le_one y
  have h4 : x^2 ≤ 3 := by
    have h5 : -1 ≤ Real.cos y := Real.neg_one_le_cos y
    rw [h1] at h5
    nlinarith
    all_goals nlinarith
  have h5 : -1 ≤ x - Real.cos y := by
    have hcos : Real.cos y = (1 - x ^ 2) / 2 := h1
    rw [hcos]
    nlinarith [sq_nonneg (x + 1), Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have h6 : x - Real.cos y ≤ Real.sqrt 3 + 1 := by
    have hcos : Real.cos y = (1 - x ^ 2) / 2 := h1
    rw [hcos]
    nlinarith [Real.sqrt_nonneg 3, sq_nonneg (x - Real.sqrt 3), sq_nonneg (x + 1 - Real.sqrt 3), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (x^2 - 3)]
  exact ⟨h5, h6⟩