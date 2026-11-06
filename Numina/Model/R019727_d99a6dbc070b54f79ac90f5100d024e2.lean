import Mathlib

theorem algebra_158998 (x y z : ℝ) (h1 : x * y = 1) (h2 : x + y + Real.cos z ^ 2 = 2) :
    x = 1 ∧ y = 1 ∧ ∃ n : ℤ, z = Real.pi / 2 + Real.pi * n := by
  have h3 : Real.cos z ^ 2 ≤ 1 := by 
    apply Real.cos_sq_le_one
  have h4 : 0 ≤ Real.cos z ^ 2 := by 
    apply sq_nonneg
  have h5 : x + y = 2 - Real.cos z ^ 2 := by
    nlinarith 
  have h6 : (x - y) ^ 2 ≥ 0 := by
    apply sq_nonneg 
  have h7 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by 
    ring 
  rw [h7, h1, h5] at h6 
  have h8 : (2 - Real.cos z ^ 2) ^ 2 - 4 ≥ 0 := by 
    nlinarith 
  have h9 : Real.cos z ^ 2 = 0 := by 
    nlinarith [h3, h4]
  have h10 : Real.cos z = 0 := by 
    nlinarith [h9]
  have h11 : ∃ n : ℤ, z = Real.pi / 2 + Real.pi * n := by 
    have h12 : Real.cos z = 0 := h10
    obtain ⟨n, hn⟩ := Real.cos_eq_zero_iff.1 h12
    refine ⟨n, by linarith [hn]⟩ 
  have h13 : x + y = 2 := by 
    have : Real.cos z ^ 2 = 0 := h9
    linarith 
  have h14 : x = 1 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), h1, h13]
  have h15 : y = 1 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), h1, h13]
  exact ⟨h14, h15, h11⟩