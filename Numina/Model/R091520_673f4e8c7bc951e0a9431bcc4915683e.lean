import Mathlib

theorem algebra_20904 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x, a * x ^ 2 + b * x + c = -1 / 9 * (x - 2) ^ 2 + 1)
    (m n : ℝ) (hm : m > n) (hmn : ∀ x, a * x ^ 2 + b * x + c = 0 → x = m ∨ x = n) :
    m - n = 6 := by
-- We pick three points to determine the coefficients of the quadratic
  have h₁ := h 0
  have h₂ := h 1
  have h₃ := h 5
  have h₄ := h (-1)
-- Solving the quadratic equation $-1/9(x-2)^2+1=0$.
  have root1 := hmn 5 (by
    rw [show a * 5 ^ 2 + b * 5 + c = -1 / 9 * (5 - 2) ^ 2 + 1 by linarith [h 5]]
    norm_num
  )
  have root2 := hmn (-1) (by
    rw [show a * (-1) ^ 2 + b * (-1) + c = -1 / 9 * (-1 - 2) ^ 2 + 1 by linarith [h (-1)]]
    norm_num
  )
  cases root1 with
  | inl hm5 =>
    cases root2 with
    | inl hm_n1 =>
      exfalso
      linarith
    | inr hn_n1 =>
      have : m - n = 6 := by
        linarith [hm5, hn_n1]
      linarith
  | inr hn5 =>
    cases root2 with
    | inl hm_n1 =>
      exfalso
      linarith
    | inr hn_n1 =>
      exfalso
      linarith [hn5, hn_n1]