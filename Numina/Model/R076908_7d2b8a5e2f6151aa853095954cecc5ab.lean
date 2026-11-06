import Mathlib

theorem algebra_533 {f : ℝ → ℝ → ℝ} (h₀ : ∀ a b, f a b = 3 * a + 2 * b)
    (u v : ℝ) (h₁ : f u v = 20) (h₂ : f v u = 20) :
    f (2 * u) (3 * v) = 48 := by 
  have eq1 : 3 * u + 2 * v = 20 := by
    rw [h₀] at h₁
    linarith
  have eq2 : 3 * v + 2 * u = 20 := by
    rw [h₀] at h₂
    linarith
  have hu : u = 4 := by 
    linarith [eq1, eq2]
  have hv : v = 4 := by 
    rw [hu] at eq1
    linarith 
  rw [h₀]
  rw [hu, hv]
  norm_num