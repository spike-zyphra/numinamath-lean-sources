import Mathlib

theorem algebra_139612 (a b c : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = 4 * x ^ 3 + a * x ^ 2 + b * x + c)
    (h₁ : ∀ x ∈ Set.Icc (-1) 1, -1 ≤ f x ∧ f x ≤ 1) :
    a = 0 ∧ b = -3 ∧ c = 0 := by
  have h1 := h₁ 1 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h2 := h₁ (-1) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h3 := h₁ 0 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h4 := h₁ (1 / 2) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h5 := h₁ (-1 / 2) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  simp [hf] at h1 h2 h3 h4 h5
  norm_num at h1 h2 h3 h4 h5
  have h6 : a = 0 := by
    nlinarith
  have h7 : b = -3 := by
    nlinarith [h6]
  have h8 : c = 0 := by
    nlinarith [h6, h7]
  exact ⟨h6, h7, h8⟩