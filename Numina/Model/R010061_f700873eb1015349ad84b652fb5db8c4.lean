import Mathlib

theorem algebra_9156 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x) (h₁ : ∀ x, f (x + 4) = f x) (h₂ : ∀ x ∈ Set.Ioo 0 2, f x = 2 * x ^ 2) : f 7 = 2 := by
  have h3 : f 7 = f 3 := by
    specialize h₁ 3
    norm_num at h₁ ⊢
    linarith
  have h4 : f 3 = f (-1) := by
    specialize h₁ (-1)
    norm_num at h₁ ⊢
    linarith
  have h6 : f (-1) = f 1 := by 
    apply h₀ 1
  have h7 : f 1 = 2 * (1 : ℝ) ^ 2 := by
    specialize h₂ 1 (by norm_num [Set.mem_Ioo])
    simpa using h₂
  rw [h3, h4, h6]
  norm_num at h7 ⊢
  all_goals linarith [h7]