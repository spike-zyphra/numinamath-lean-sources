import Mathlib
open Real

theorem algebra_5070 {f : ℝ → ℝ} (h : ∀ x y, (x - y) * f (x + y) - (x + y) * f (x - y) = 4 * x * y * (x ^ 2 - y ^ 2))
    (h' : ∀ x y, (f (x + y)) / (x + y) - (x + y) ^ 2 = (f (x - y)) / (x - y) - (x - y) ^ 2) :
    ∃ c, ∀ x, x ≠ 0 → (f x) / x - x ^ 2 = c := by
  use (f 1 / 1 - 1 ^ 2)
  intro x hx
  have h1 := h' ((x + 1) / 2) ((x - 1) / 2)
  have eq1 : ((x + 1) / 2 + (x - 1) / 2 : ℝ) = x := by
    ring_nf
  have eq2 : ((x + 1) / 2 - (x - 1) / 2 : ℝ) = (1 : ℝ) := by
    ring_nf
  have eq3 : (f ((x + 1) / 2 + (x - 1) / 2) ) / ((x + 1) / 2 + (x - 1) / 2 : ℝ) - ((x + 1) / 2 + (x - 1) / 2 : ℝ) ^ 2 = 
      (f ((x + 1) / 2 - (x - 1) / 2) ) / ((x + 1) / 2 - (x - 1) / 2 : ℝ) - ((x + 1) / 2 - (x - 1) / 2 : ℝ) ^ 2 := by 
    simpa using h1
  rw [eq1] at eq3
  rw [eq2] at eq3
  have hx1 : x ≠ 0 := hx
  field_simp [hx1] at eq3 ⊢
  <;> linarith
  all_goals field_simp [hx1] at *