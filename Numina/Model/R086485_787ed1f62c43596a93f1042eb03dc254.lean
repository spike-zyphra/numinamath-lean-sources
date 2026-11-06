import Mathlib

theorem algebra_170539 (a : Fin 11 → ℝ) (h₀ : ∀ i j k, i + 1 = j ∧ j + 1 = k → a i + a j + a k = 18)
    (h₁ : ∑ i, a i = 64) : a 5 = 8 := by

  have eq1 := h₀ 0 1 2 (by simp)
  have eq2 := h₀ 1 2 3 (by simp)
  have eq3 := h₀ 2 3 4 (by simp)
  have eq4 := h₀ 3 4 5 (by simp)
  have eq5 := h₀ 4 5 6 (by simp)
  have eq6 := h₀ 5 6 7 (by simp)
  have eq7 := h₀ 6 7 8 (by simp)
  have eq8 := h₀ 7 8 9 (by simp)
  have eq9 := h₀ 8 9 10 (by simp)

  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h₁
  norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 
  norm_num at h₁
  
  linarith