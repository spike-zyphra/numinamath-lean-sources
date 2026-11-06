import Mathlib

theorem algebra_276201 {a b c p x : ℝ} (h₀ : a + b + c = 2 * p)
    (h₁ : x = (b ^ 2 + c ^ 2 - a ^ 2) / (2 * c)) (h₂ : c ≠ 0) :
    b ^ 2 - x ^ 2 = (4 / c ^ 2) * (p * (p - a) * (p - b) * (p - c)) := by
  have hp : p = (a + b + c) / 2 := by linarith
  rw [h₁] -- Substitute x
  rw [hp] -- Substitute p
  field_simp
  ring_nf
  <;> nlinarith [h₀]