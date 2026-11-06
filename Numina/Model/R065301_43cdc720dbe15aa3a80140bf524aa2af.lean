import Mathlib

theorem algebra_3965 {x y z : ℝ} (h₀ : x / 3 = y / 4) (h₁ : y / 4 = z / 5) (h₂ : 7 * x + 10 * y + 8 * z = 2020) :
    x + 3 * y - 5 * z = -200 := by
  have h3 : 4 * x = 3 * y := by
    field_simp at h₀
    linarith
  have h4 : 5 * y = 4 * z := by
    field_simp at h₁
    linarith
  have h5 : y = 4 / 3 * x := by
    linarith
  have h6 : z = 5 / 3 * x := by
    have : z = 5 / 4 * y := by
      linarith
    rw [this]
    rw [h5]
    ring
  rw [show y = 4 / 3 * x by linarith [h5]] at h₂
  rw [show z = 5 / 3 * x by linarith [h6]] at h₂
  have hx : x = 60 := by
    linarith
  have hy : y = 80 := by
    rw [hx] at h5
    linarith
  have hz : z = 100 := by
    rw [hx] at h6
    linarith
  rw [hx, hy, hz]
  norm_num