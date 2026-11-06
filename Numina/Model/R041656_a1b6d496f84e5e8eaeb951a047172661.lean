import Mathlib

theorem calculus_22608 (θ : ℝ) (h : θ ≠ 0) (f : ℝ × ℝ → ℝ × ℝ)
    (hf : f = fun (x, y) => (x * Real.cos θ - y * Real.sin θ, x * Real.sin θ + y * Real.cos θ))
    (h1 : f (-4, 7) = (1, 8)) :
    f (-1, 3) = (1, 3) := by 
  have eq1 : -4 * Real.cos θ - 7 * Real.sin θ = 1 := by 
    rw [hf] at h1
    simp at h1 
    linarith
  have eq2 : -4 * Real.sin θ + 7 * Real.cos θ = 8 := by 
    rw [hf] at h1 
    simp at h1 
    nlinarith
  have h3 : Real.sin θ = -3 / 5 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have h4 : Real.cos θ = 4 / 5 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, h3]
  have h5 : f (-1, 3) = (1, 3) := by 
    rw [hf]
    simp [h4, h3]
    all_goals norm_num 
  exact h5