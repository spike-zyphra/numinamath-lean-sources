import Mathlib

theorem algebra_287890 (f : ℝ → ℝ)
    (h₀ : ∀ x ∈ Set.Icc 0 1, f (1 - x) = 1 - f x)
    (h₁ : ∀ x ∈ Set.Icc 0 1, f (x / 3) = (1 / 2) * f x)
    (h₂ : ∀ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 → f a ≤ f b) :
    f (6 / 7) = 3 / 4 := by 
  have h7 : f 0 = 0 := by
    have h8 : f (0 / 3) = (1 / 2) * f 0 := h₁ 0 (by norm_num)
    norm_num at h8
    linarith
  have h8 : f 1 = 1 := by
    have h9 : f (1 - 0 : ℝ) = 1 - f 0 := h₀ 0 (by norm_num)
    rw [show (1 - 0 : ℝ) = 1 by norm_num, h7] at h9 
    linarith
  have h9 : f (1 / 3 : ℝ) = 1 / 2 := by
    specialize h₁ 1 (by norm_num)
    norm_num [h8] at h₁ ⊢
    linarith
  have h10 : f (2 / 3 : ℝ) = 1 / 2 := by
    specialize h₀ (1 / 3 : ℝ) (by norm_num)
    norm_num at h₀ ⊢
    linarith [h9]
  have h11 : f (1 / 9 : ℝ) = 1 / 4 := by
    specialize h₁ (1 / 3 : ℝ) (by norm_num)
    norm_num at h₁ ⊢
    linarith [h9]
  have h12 : f (2 / 9 : ℝ) = 1 / 4 := by
    specialize h₁ (2 / 3 : ℝ) (by norm_num)
    norm_num at h₁ ⊢
    linarith [h10]
  have h3 : f (1 - (6 / 7 : ℝ)) = 1 - f (6 / 7 : ℝ) := h₀ (6 / 7) (by norm_num)
  have h4 : (1 - (6 / 7 : ℝ) ) = (1 / 7 : ℝ) := by norm_num
  have h5 : f (1 - (1 / 7 : ℝ) ) = 1 - f (1 / 7 : ℝ) := h₀ (1 / 7) (by norm_num)
  have h6 : (1 - (1 / 7 : ℝ) ) = (6 / 7 : ℝ) := by norm_num
  -- Show f (1 / 7) ≤ 1 / 4.
  have h13 : f (1 / 7 : ℝ) ≤ 1 / 4 := by
    have h9c : f (1 / 7 : ℝ) ≤ f (2 / 9 : ℝ) := by
      apply h₂
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    linarith [h12, h9c]

  -- Show f (1 / 7) ≥ 1 / 4.
  have h14a : f (1 / 7 : ℝ) ≥ 1 / 4 := by
    have h6a : f (1 / 9 : ℝ) ≤ f (1 / 7 : ℝ) := by
      apply h₂
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    linarith [h11, h6a]
  
  -- f (1 / 7) = 1 / 4
  have h13a : f (1 / 7 : ℝ) = 1 / 4 := by 
    linarith [h14a, h13]
  rw [h4] at h3 
  rw [h13a] at h3 
  linarith