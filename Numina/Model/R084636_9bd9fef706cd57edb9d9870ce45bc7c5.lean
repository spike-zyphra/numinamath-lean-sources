import Mathlib

theorem algebra_177255 {f : ℝ → ℝ} (hf : ∀ x, f x = (x - 1) * x / 2)
    (x0 : ℝ) (hx0 : x0 ≠ 0) :
    f (x0 + 2) = (x0 + 2) * f (x0 + 1) / x0 := by 
  have h1 : f (x0 + 1) = (x0 * (x0 + 1)) / 2 := by
    rw [hf]
    ring
  have h2 : f (x0 + 2) = ((x0 + 1) * (x0 + 2)) / 2 := by
    rw [hf]
    ring
  rw [h2, h1]
  field_simp [hx0]
  <;> ring