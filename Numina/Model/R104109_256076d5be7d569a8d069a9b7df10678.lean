import Mathlib

theorem algebra_178190 {a b c : ℝ} (h : a ≠ b ∧ b ≠ c ∧ a ≠ c)
    (h' : a / (b - c) + b / (c - a) + c / (a - b) = 0) :
    a / (b - c)^2 + b / (c - a)^2 + c / (a - b)^2 = 0 := by
  have h1 : a ≠ b := h.1
  have h2 : b ≠ c := h.2.1
  have h3 : a ≠ c := h.2.2

  have hbc : b - c ≠ 0 := by
    intro h₀
    have : b = c := by linarith
    contradiction

  have hab : a - b ≠ 0 := by
    intro h₀
    have : a = b := by linarith
    contradiction

  have hca : c - a ≠ 0 := by
    intro h₀
    have : a = c := by linarith
    contradiction

  have eq1 : a * (c - a) * (a - b) + b * (b - c) * (a - b) + c * (b - c) * (c - a) = 0 := by 
    have h1' : a / (b - c) + b / (c - a) + c / (a - b) = 0 := h'
    field_simp [show b - c ≠ 0 by exact hbc, show c - a ≠ 0 by exact hca, show a - b ≠ 0 by exact hab] at h1' ⊢
    <;> ring_nf at h1' ⊢
    <;> nlinarith

  have eq2 : a / (b - c)^2 + b / (c - a)^2 + c / (a - b)^2 = 0 := by
    have eq1' := eq1
    field_simp [show b - c ≠ 0 by exact hbc, show c - a ≠ 0 by exact hca, show a - b ≠ 0 by exact hab]
    <;> ring_nf at eq1' ⊢
    <;> nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

  linarith [eq2]