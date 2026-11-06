import Mathlib

theorem algebra_328463 (a b : ℝ) (h : ∀ x ∈ Set.Icc 0 1, |a * x + b| ≤ 1) :
    |20 * a + 14 * b| + |20 * a - 14 * b| ≤ 80 := by
  have h1 := h 0 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h2 := h 1 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h3 := h (1 / 2) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h4 := h (7 / 10) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h5 := h (1 / 10) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h6 := h (9 / 10) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  cases' abs_cases (20 * a + 14 * b) with h7 h7 <;> 
  cases' abs_cases (20 * a - 14 * b) with h8 h8 <;> 
  try { 
    linarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, abs_le.mp h4, abs_le.mp h5, abs_le.mp h6]
  }