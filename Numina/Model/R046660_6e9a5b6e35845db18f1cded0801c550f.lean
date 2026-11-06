import Mathlib

theorem algebra_70086 {x y z a : ℝ} (h₀ : x * 3 = y * 2) (h₁ : y * 5 = z * 3) (h₂ : x + y + z = 100)
    (h₃ : y = a * x - 10) : a = 2 := by
  have hx1 : y = (3 / 2) * x := by
    linarith
  have hx2 : z = (5 / 2) * x := by
    rw [hx1] at h₁
    linarith
  have hx3 : x = 20 := by
    have eq1 : x + y + z = 100 := h₂
    rw [show y = (3 / 2) * x by linarith, show z = (5 / 2) * x by linarith] at eq1
    linarith
  have hx4 : y = 30 := by
    rw [hx3] at hx1
    linarith
  have hx5 : a = 2 := by
    rw [hx4, hx3] at h₃
    linarith
  exact hx5