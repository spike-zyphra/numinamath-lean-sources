import Mathlib

theorem algebra_206798 {x y : ℝ} (h1 : x^2 = 2 * y - 1) (h2 : x^4 + y^4 = 2) :
    x = 1 ∧ y = 1 ∨ x = -1 ∧ y = 1 := by
  have eq1 : x^2 = 2 * y - 1 := h1
  have eq2 : x^4 + y^4 = 2 := h2
  have eq3 : x^4 = (2 * y - 1) ^ 2 := by
    calc
      x^4 = (x ^ 2) ^ 2 := by ring
      _ = (2 * y - 1) ^ 2 := by rw [eq1]
  rw [eq3] at eq2
  have h3 : y ^ 4 + 4 * y ^ 2 - 4 * y - 1 = 0 := by
    nlinarith [eq2]
  have h4 : (y - 1) * (y ^ 3 + y ^ 2 + 5 * y + 1) = 0 := by
    nlinarith [sq_nonneg (y ^ 2 - 1), sq_nonneg (y ^ 2 - 2 * y)]
  cases' (mul_eq_zero.mp h4) with hy1 hy2
  · -- Case where $y - 1 = 0$, which means $y = 1$
    have hy : y = 1 := by linarith
    have hx2 : x^2 = 1 := by
      rw [hy] at h1
      linarith
    have hx : x = 1 ∨ x = -1 := by
      have h : x^2 - 1 = 0 := by linarith
      have : (x - 1) * (x + 1) = 0 := by
        linarith [h]
      cases' (mul_eq_zero.mp this) with hx1 hx2
      · -- Case where $x - 1 = 0$, so $x = 1$
        left
        linarith
      · -- Case where $x + 1 = 0$, so $x = -1$
        right
        linarith
    cases hx with
    | inl hx1 =>
      left
      exact ⟨hx1, hy⟩
    | inr hx2 =>
      right
      exact ⟨hx2, hy⟩
  · -- Case where the cubic polynomial equals zero
    -- We need to derive a contradiction in this case
    have hy3 : y ^ 3 + y ^ 2 + 5 * y + 1 = 0 := by linarith
    nlinarith [sq_nonneg (y + 1 / 2), sq_nonneg (x), sq_nonneg (y - 1), sq_nonneg (x^2 - 1)]