import Mathlib

theorem calculus_17200 (k : ℝ) (x y z : ℝ)
    (h₀ : x ≠ 0) (h₁ : y ≠ 0) (h₂ : z ≠ 0)
    (h₃ : x + k * y + 3 * z = 0) (h₄ : 3 * x + k * y - 2 * z = 0)
    (h₅ : 2 * x + 4 * y - 3 * z = 0) :
    x * z / y ^ 2 = 10 := by

  have eq1 : 2 * x - 5 * z = 0 := by
    linarith

  have hx1 : x = 5 / 2 * z := by
    linarith

  have eq2 : 2 * x + 4 * y - 3 * z = 0 := by
    linarith

  rw [hx1] at eq2

  have hy1 : y = -1 / 2 * z := by
    linarith

  have h6 : x * z = (5 / 2) * z ^ 2 := by
    rw [hx1]
    linarith

  have h7 : y ^ 2 = (1 / 4) * z ^ 2 := by
    rw [hy1]
    ring_nf

  have h8 : z ^ 2 ≠ 0 := by
    apply pow_ne_zero 2
    exact h₂

  have h9 : (x * z) / y ^ 2 = 10 := by
    rw [h6, h7]
    have h10 : z ^ 2 ≠ 0 := h8
    field_simp [h10]
    <;> nlinarith

  exact h9