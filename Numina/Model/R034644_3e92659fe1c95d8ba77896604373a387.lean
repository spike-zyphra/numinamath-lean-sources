import Mathlib

theorem algebra_97928 {m n : ℝ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n)
    (h : ∀ x, (x + m) ^ 2 - (x + n) ^ 2 = (m - n) ^ 2) :
    ∃! a, ∃! b, a ≠ 0 ∧ b ≠ 0 ∧ x = a * m + b * n := by
  have h0 := h 0
  have eq1 : m ^ 2 - n ^ 2 = (m - n) ^ 2 := by
    linarith
  have eq2 : (m - n) ^ 2 = m ^ 2 - 2 * m * n + n ^ 2 := by
    ring
  rw [eq2] at eq1
  have eq3 : 2 * m * n - 2 * n ^ 2 = 0 := by
    linarith
  have eq4 : 2 * n * (m - n) = 0 := by
    linarith [eq3]
  have eq5 : m - n = 0 := by
    apply (mul_left_inj' (hn)).mp
    linarith
  have eq6 : m = n := by
    linarith
  have eq7 : m ≠ n := hmn
  contradiction