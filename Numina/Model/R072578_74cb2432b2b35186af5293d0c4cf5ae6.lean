import Mathlib

theorem algebra_14010 (a : ℝ) :
    (∀ x ∈ Set.Icc (-1) 1, x ^ 2 + a * x + 3 > a) ↔ a < 2 := by
  constructor
  · -- Assume that ∀ x ∈ [-1,1], x^2 + a*x + 3 > a, prove that a < 2
    intro h
    have h1 := h (-1) (Set.left_mem_Icc.mpr (by norm_num))
    norm_num at h1
    linarith
  · -- Assume a < 2, prove ∀ x ∈ [-1,1], x^2 + a*x + 3 > a
    intro ha x hx
    rcases hx with ⟨hx1, hx2⟩
    nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (a - 2),
      mul_nonneg ((show 0 ≤ (1 - x) by linarith)) ((show 0 ≤ (1 + x) by linarith)), sq_nonneg (x - (-a / 2)), sq_nonneg (x), sq_nonneg (a - 4)]