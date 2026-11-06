import Mathlib

theorem algebra_177180 {f : ℝ → ℝ → ℝ}
    (h₀ : ∀ x y, f x y = f y x)
    (h₁ : ∀ x y z, f x y * z = f (x * z) (y * z))
    (h₂ : ∀ x y z, f x y + z = f (x + z) (y + z)) :
    f 1975 1976 = 1975.5 := by
  have eq1 : f 1975 1976 = 1975 + f 0 1 := by
    specialize h₂ 1975 1976 (-1975)
    norm_num at h₂ ⊢
    linarith
  have eq2 : f 0 0 = 0 := by 
    specialize h₁ 0 0 (0 : ℝ)
    norm_num at h₁ ⊢
    linarith
  have eq3 : f 1 1 = 1 := by 
    specialize h₂ 0 0 1
    rw [eq2] at h₂
    norm_num at h₂ ⊢
    linarith
  -- Derive f(0,1) = 0.5
  have eq4 : f 0 1 = 0.5 := by 
    have eq5 : f 0 1 * (-1) = f 0 (-1) := by
      specialize h₁ 0 1 (-1)
      norm_num at h₁ ⊢
      linarith
    have eq7 : f 0 1 - 1 = f (-1) 0 := by 
      specialize h₂ 0 1 (-1)
      norm_num at h₂ ⊢
      linarith
    have eq8 : f 0 (-1) = f (-1) 0 := by 
      rw [h₀]
    -- Combine eq5 and eq8
    have eq9 : f 0 1 * (-1) = f (-1) 0 := by
      have eq7' : f 0 (-1) = f (-1) 0 := eq8
      linarith [eq5, eq7']
    -- Now combine with eq7
    have eq10 : f 0 1 * (-1) = f 0 1 - 1 := by
      have eq7' : f 0 1 - 1 = f (-1) 0 := eq7
      linarith [eq9, eq7']
    -- Now solve
    have eq11 : f 0 1 = 1 / 2 := by 
      linarith
    rw [eq11]
    norm_num
  rw [eq1]
  rw [eq4]
  all_goals norm_num