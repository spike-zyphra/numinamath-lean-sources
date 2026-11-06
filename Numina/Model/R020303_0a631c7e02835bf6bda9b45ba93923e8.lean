import Mathlib

theorem algebra_312784 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x)
    (hf : ∀ x, f (x + 2) = f x) (hf' : ∀ x ∈ Set.Ioo 0 1, f x = x ^ 2) :
    f (-3 / 2) + f 1 = 1 / 4 := by
  have h1 : f (-3 / 2) = - f (3 / 2) := by 
    have h2 := hodd (3 / 2)
    ring_nf at h2 ⊢ 
    linarith

  have h2 : f (3 / 2) = f (-1 / 2) := by 
    have h3 : f (-1 / 2) = f ((-1 / 2 : ℝ) + 2) := by 
      rw [hf (-1 / 2)]
    have h4 : (-1 / 2 : ℝ) + 2 = (3 / 2 : ℝ) := by 
      norm_num
    rw [h4] at h3
    linarith

  have h3 : f (-1 / 2) = - f (1 / 2) := by 
    have h4 := hodd (1 / 2)
    ring_nf at h4 ⊢ 
    linarith

  have h4 : f (1 / 2) = (1 / 2) ^ 2 := by 
    specialize hf' (1 / 2) (by norm_num)
    linarith

  have h5 : f 1 = 0 := by
    have h6 : f 1 = f (-1) := by
      have h7 : f (-1) = f ((-1 : ℝ) + 2) := by
        rw [hf (-1)]
      have h8 : (-1 : ℝ) + 2 = (1 : ℝ) := by
        norm_num
      rw [h8] at h7 
      linarith
    have h8 : f (-1) = - f 1 := by 
      apply hodd 
    rw [h8] at h6 
    linarith

  have h6 : f (-3 / 2) = 1 / 4 := by
    rw [h1]
    rw [h2]
    rw [h3]
    rw [h4]
    all_goals norm_num

  rw [h6]
  rw [h5]
  all_goals norm_num