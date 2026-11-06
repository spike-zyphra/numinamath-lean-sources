import Mathlib

theorem algebra_282922 {q : ℝ} (h : ∃ x, x^2 - 3 * x + q = 0 ∧ ∀ y, y^2 - 3 * y + q = 0 → x = y) :
    q = 9 / 4 := by
  rcases h with ⟨x, hx1, hx2⟩
  have h_eq : x^2 - 3 * x + q = 0 := hx1
  have hy : (3 - x) ^ 2 - 3 * (3 - x) + q = 0 := by
    have h_eq1 : x ^ 2 - 3 * x + q = 0 := h_eq
    nlinarith
  have hx_eq_y : x = 3 - x := by
    apply hx2 (3 - x) 
    linarith [hy]
  have hx_val : x = 3 / 2 := by
    nlinarith 
  rw [hx_val] at h_eq 
  nlinarith 
  all_goals nlinarith 
  all_goals nlinarith
  all_goals nlinarith 
  all_goals nlinarith