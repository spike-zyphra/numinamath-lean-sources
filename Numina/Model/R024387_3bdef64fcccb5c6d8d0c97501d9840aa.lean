import Mathlib

theorem algebra_601506 {f g : ℝ → ℝ} (hf : ∀ x y, Real.sin x + Real.cos y = f x + f y + g x - g y) :
    ∃ c, ∀ x, f x = (Real.sin x + Real.cos x) / 2 ∧ g x = (Real.sin x - Real.cos x) / 2 + c := by
  use (g 0 + 1 / 2)
  intro x 
  constructor
  · -- Show that $f(x) = \frac{\sin x + \cos x}{2}$
    have h1 := hf x x 
    simp at h1 
    linarith 
  · -- Show that $g(x) = \frac{\sin x - \cos x}{2} + c$
    have eq1 := hf x 0
    have eq2 : Real.sin 0 = 0 := by simp [Real.sin_zero]
    have eq3 : Real.cos 0 = 1 := by simp [Real.cos_zero]
    simp [eq2, eq3] at eq1 
    have eq4 : f x = (Real.sin x + Real.cos x) / 2 := by 
      have h1 := hf x x 
      simp at h1 
      linarith 
    have eq5 : f 0 = (Real.sin (0 : ℝ) + Real.cos (0 : ℝ)) / 2 := by 
      have h1 := hf 0 0 
      simp at h1 
      linarith 
    have eq6 : f 0 = 1 / 2 := by 
      rw [eq5]
      norm_num [Real.sin_zero, Real.cos_zero]
    linarith [eq4, eq6, eq1]