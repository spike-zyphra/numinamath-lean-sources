import Mathlib

theorem algebra_241068 {f : ℝ → ℝ} (hf : ∀ x ∈ Set.Icc 0 1, ∀ y ∈ Set.Icc 0 1, x < y → f x ≤ f y)
    (h0 : f 0 = 0) (h1 : ∀ x ∈ Set.Icc 0 1, f (x / 3) = (1 / 2) * f x) (h2 : ∀ x ∈ Set.Icc 0 1, f (1 - x) = 1 - f x) :
    f (5 / 12) + f (1 / 8) = 3 / 4 := by
  have f1 : f 1 = 1 := by
    have h20 := h2 0 (by norm_num)
    norm_num at h20
    linarith [h0]
  have f1_3 : f (1 / 3) = 1 / 2 := by
    specialize h1 1 (by norm_num)
    norm_num at h1 ⊢
    linarith [f1]
  have f2_3 : f (2 / 3) = 1 / 2 := by
    specialize h2 (1 / 3) (by norm_num)
    norm_num at h2 ⊢
    linarith [f1_3]
  have f5_12 : f (5 / 12) = 1 / 2 := by
    have h5 : f (1 / 3) ≤ f (5 / 12) := by
      apply hf
      all_goals norm_num
    have h5' : f (5 / 12) ≤ f (2 / 3) := by
      apply hf
      all_goals norm_num
    linarith [f1_3, f2_3, h5, h5']
  have f3_8 : f (3 / 8) = 1 / 2 := by
    have h15 : f (1 / 3) ≤ f (3 / 8) := by
      apply hf
      all_goals norm_num
    have h15' : f (3 / 8) ≤ f (2 / 3) := by
      apply hf
      all_goals norm_num
    linarith [f1_3, f2_3, h15, h15']
  have h15 : f (1 / 8) = (1 / 2) * f (3 / 8) := by
    specialize h1 (3 / 8) (by norm_num)
    norm_num at h1 ⊢
    linarith [h1]
  have f1_8 : f (1 / 8) = 1 / 4 := by
    rw [h15]
    linarith [f3_8]
  linarith [f5_12, f1_8]