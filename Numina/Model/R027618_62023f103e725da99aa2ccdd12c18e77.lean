import Mathlib

theorem algebra_11708 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x, f (x + 2) = f x)
    (hf' : ∀ x ∈ Set.Ioo 0 1, f x = x ^ 2) :
    f (-3 / 2) + f 1 = 1 / 4 := by
  have h1 : f 1 = 0 := by
    have h2 : f 1 = f (-1 : ℝ) := by
      have h3 := hf (-1 : ℝ)
      norm_num at h3 ⊢
      linarith
    have h4 : f (-1 : ℝ) = - f 1 := by
      specialize hodd 1
      linarith
    linarith [h2, h4]
  have h5 : f (-3 / 2 : ℝ) = f (1 / 2 : ℝ) := by
    have h7 : f (-3 / 2 : ℝ) = f ((-3 / 2 : ℝ) + 2) := by
      have h8 : f ((-3 / 2 : ℝ) + 2) = f (-3 / 2 : ℝ) := hf (-3 / 2 : ℝ)
      linarith [h8]
    have h6 : (-3 / 2 : ℝ) + 2 = (1 / 2 : ℝ) := by
      norm_num
    rw [h6] at h7
    linarith
  have h8 : f (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ 2 := by
    have h9 : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) (1 : ℝ) := by
      constructor
      · norm_num
      · norm_num
    specialize hf' (1 / 2 : ℝ) h9
    linarith [hf']
  have h9 : f (1 / 2 : ℝ) = (1 / 4 : ℝ) := by
    rw [h8]
    norm_num
  have h10 : f (-3 / 2 : ℝ) = (1 / 4 : ℝ) := by
    linarith [h5, h9]
  linarith [h10, h1]