import Mathlib

theorem algebra_52826 (m : ℝ) (h : ∃ x1 x2, x1 ≠ x2 ∧ 5 * m * x1 = 2 * x1 ^ 2 - 9 * x1 + 10 ∧ 5 * m * x2 = 2 * x2 ^ 2 - 9 * x2 + 10 ∧ x1 + x2 = 77) :
    m = 29 := by
  rcases h with ⟨x1, x2, hx12, heq1, heq2, hsum⟩
  have eq1 : 2 * x1 ^ 2 - (9 + 5 * m) * x1 + 10 = 0 := by
    linarith
  have eq2 : 2 * x2 ^ 2 - (9 + 5 * m) * x2 + 10 = 0 := by
    linarith
  have eq3 : 2 * (x1 ^ 2 - x2 ^ 2) - (9 + 5 * m) * (x1 - x2) = 0 := by
    nlinarith [eq1, eq2]
  have : (x1 - x2) * (2 * (x1 + x2) - (9 + 5 * m)) = 0 := by
    ring_nf at eq3 ⊢
    linarith
  cases' (mul_eq_zero.mp this) with h1 h2
  · -- Case where x1 - x2 = 0, which would imply x1 = x2
    exfalso
    have h2' : x1 = x2 := by linarith
    exact hx12 (by linarith)
  · -- Case where 2(x1 + x2) - (9 + 5m) = 0
    have eq4 : 2 * (x1 + x2) - (9 + 5 * m) = 0 := by
      linarith
    rw [hsum] at eq4
    nlinarith