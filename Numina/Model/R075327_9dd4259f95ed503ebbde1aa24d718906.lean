import Mathlib

theorem algebra_180987 {x y z : ℕ} (h₀ : x * y * z = 13600) (h₁ : x * z = 544) (h₂ : y * z = 425) :
    x * y = 800 := by
  have h3 : y = 25 := by
    have h_eq : x * y * z = (x * z) * y := by
      ring
    rw [h_eq] at h₀
    rw [h₁] at h₀
    nlinarith
  have h4 : z = 17 := by
    rw [h3] at h₂
    nlinarith
  have h5 : x = 32 := by
    rw [h4] at h₁
    nlinarith
  calc
    x * y = 32 * 25 := by rw [h5, h3]
    _ = 800 := by norm_num