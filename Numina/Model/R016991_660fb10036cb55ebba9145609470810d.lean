import Mathlib

theorem algebra_159452 {f : ℤ → ℝ} (hf : ∀ x, f x = (5 / 3) * x - (1 / 3)) :
    ∀ k, f (3 * k + 2) = 5 * k + 3 := by 
  intro k 
  rw [hf]
  simp [mul_add, add_mul]
  ring_nf
  <;> norm_num