import Mathlib

theorem algebra_165613 {x : ℝ} (hx : x ≠ 0) (hx' : x^2 + 1 ≠ 0) :
    (x^2 + 1)/x + x/(x^2 + 1) = -2.5 ↔ x = -1 := by
  constructor
  · -- Assume (x^2 + 1)/x + x/(x^2 + 1) = -2.5, prove x = -1
    intro h
    have h₁ : (x^2 + 1) / x + x / (x^2 + 1) = -2.5 := h
    have eq1 : (x ^ 2 + 1) ^ 2 + x ^ 2 = -2.5 * (x * (x ^ 2 + 1)) := by
      have h2 : x * (x ^ 2 + 1) ≠ 0 := by
        apply mul_ne_zero
        · exact hx
        · exact hx'
      field_simp [h2] at h₁ ⊢
      nlinarith
    have eq2 : (x + 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x ^ 2 + 1 - 1)]
    have eq3 : x + 1 = 0 := by
      simp at eq2 ⊢
      exact eq2
    have hx_eq : x = -1 := by linarith
    exact hx_eq
  · -- Assume x = -1, prove (x^2 + 1)/x + x/(x^2 + 1) = -2.5
    intro h
    rw [h]
    norm_num