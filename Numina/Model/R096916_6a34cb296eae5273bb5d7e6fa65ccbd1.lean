import Mathlib

theorem algebra_95757 {b d : ℝ} (h₀ : b = d - 12.50) (h₁ : b * 100 = d * 100 - 25) :
    b + d = 87.50 := by
  rw [h₀] at h₁ -- substitute b = d - 12.50 into h₁
  ring_nf at h₁
  linarith -- solve the resulting contradiction