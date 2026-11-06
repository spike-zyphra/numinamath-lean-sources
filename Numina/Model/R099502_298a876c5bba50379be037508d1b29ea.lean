import Mathlib

theorem algebra_317433 (a b : ℝ) (f : ℝ → ℝ) (hf : ∀ x ∈ Set.Icc 0 1, |f x| ≤ 1)
    (h₀ : ∀ x, f x = a * x + b) :
    a * b ≤ 1 / 4 := by
  have h1 := hf 0 (Set.left_mem_Icc.mpr (by norm_num))
  have h2 := hf 1 (Set.right_mem_Icc.mpr (by norm_num))
  have h3 := hf (1 / 2) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  simp [h₀] at h1 h2 h3
  cases' abs_le.mp h1 with h1_neg h1_pos
  cases' abs_le.mp h2 with h2_neg h2_pos
  cases' abs_le.mp h3 with h3_neg h3_pos
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), 
          sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2)]