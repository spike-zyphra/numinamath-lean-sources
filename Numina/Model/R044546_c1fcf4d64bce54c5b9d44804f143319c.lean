import Mathlib

theorem algebra_293536 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : y ≠ 0) (h₂ : z ≠ 0)
    (h₃ : ∃ r, 4 * y = 3 * x * r ∧ 5 * z = 4 * y * r)
    (h₄ : ∃ d, 1 / y = 1 / x + d ∧ 1 / z = 1 / y + d) :
    x / z + z / x = 34 / 15 := by
  rcases h₃ with ⟨r, h₅, h₆⟩
  rcases h₄ with ⟨d, h₇, h₈⟩
  have eq1 : 1 / z + 1 / x = 2 * (1 / y) := by
    have eq2 : d = (1 / y - 1 / x) := by
      linarith
    have eq3 : 1 / z = 1 / y + d := by linarith
    rw [eq2] at eq3
    linarith
  have eq2 : y * (x + z) = 2 * x * z := by
    have h8 : 1 / z + 1 / x = 2 * (1 / y) := eq1
    field_simp [h₀, h₁, h₂] at h8 ⊢
    linarith
  have eq3 : 16 * y ^ 2 = 15 * x * z := by
    have eq4 : 4 * y = 3 * x * r := h₅
    have eq5 : 5 * z = 4 * y * r := h₆
    have h9 : r = (4 * y) / (3 * x) := by
      have hx : x ≠ 0 := h₀
      field_simp [hx]
      linarith
    rw [h9] at eq5
    have hx : x ≠ 0 := h₀
    have hy : y ≠ 0 := h₁
    field_simp [hx] at eq5 ⊢
    nlinarith
  have eq4 : 15 * (x + z) ^ 2 - 64 * (x * z) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show y ≠ 0 by exact h₁), sq_pos_of_ne_zero (show x ≠ 0 by exact h₀), sq_pos_of_ne_zero (show z ≠ 0 by exact h₂)]
  have eq5 : 15 * x ^ 2 - 34 * x * z + 15 * z ^ 2 = 0 := by
    nlinarith
  have eq7 : x / z + z / x = (x ^ 2 + z ^ 2) / (x * z) := by
    field_simp [h₀, h₂]
    <;> ring
  have eq8 : (x ^ 2 + z ^ 2) / (x * z) = 34 / 15 := by
    have eq9 : x ^ 2 + z ^ 2 = (34 / 15) * (x * z) := by
      nlinarith
    have h10 : x * z ≠ 0 := by
      apply mul_ne_zero
      exact h₀
      exact h₂
    field_simp [h10]
    nlinarith
  rw [eq7]
  linarith [eq8]