import Mathlib

theorem algebra_126724 (x y z : ℝ) (h₀ : x + 5 * y - z + 11 = 0) (h₁ : x - y + 2 * z - 1 = 0) :
    (x + 1) / 9 = (y + 2) / -3 ∧ (y + 2) / -3 = z / -6 := by 
  constructor
  · -- Prove (x + 1) / 9 = (y + 2) / -3
    have h2 : x = -7 - 3 * y := by
      linarith [h₀, h₁]
    rw [h2]
    field_simp
    ring
  · -- Prove (y + 2) / -3 = z / -6
    have h3 : z = 2 * y + 4 := by
      rw [show x = -7 - 3 * y by linarith [h₀, h₁]] at h₀
      linarith
    rw [h3]
    field_simp
    ring