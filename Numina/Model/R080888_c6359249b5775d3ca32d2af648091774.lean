import Mathlib

theorem algebra_107579 (k b : ℝ) (h : ∃ x, x ≠ 0 ∧ 7 * x + (3 + x) = k + b * x ∧
    ∃ y, y ≠ 0 ∧ 7 * y + (3 + y) = k - b * y ∧ x = y / 3) :
    b = -4 := by
  rcases h with ⟨x, hx1, h1, ⟨y, hy1, h2, h3⟩⟩
  have eq1 : 8 * x + 3 = k + b * x := by
    linarith
  have eq2 : 8 * y + 3 = k - b * y := by
    linarith
  have hy_eq : y = 3 * x := by
    linarith
  rw [hy_eq] at eq2
  have eq_k : k = 8 * x + 3 - b * x := by
    linarith
  rw [eq_k] at eq2
  have h4 : 16 * x = -4 * b * x := by 
    linarith
  have hb : b = -4 := by 
    apply (mul_left_inj' hx1).mp
    linarith
  exact hb