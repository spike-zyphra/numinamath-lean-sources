import Mathlib

theorem algebra_247282 {c : ℝ} (h : ∃ x y, x ≠ 0 ∧ y ≠ 0 ∧ x / y = -3 / 4 ∧ 4 * x ^ 2 - 5 * x + c = 0 ∧ 4 * y ^ 2 - 5 * y + c = 0) :
    c = -75 := by
  rcases h with ⟨x, y, hx1, hy1, h1, h2, h3⟩
  have h4 : x = -3 / 4 * y := by
    have hne : y ≠ 0 := hy1
    field_simp [hne] at h1
    linarith
  rw [h4] at h2
  have eq1 : 9 * y ^ 2 + 15 * y + 4 * c = 0 := by 
    nlinarith
  have eq2 : 4 * y ^ 2 - 5 * y + c = 0 := by
    nlinarith
  have eq3 : c = 5 * y - 4 * y^2 := by 
    nlinarith
  rw [eq3] at eq1
  have eq4 : -7 * y^2 + 35 * y = 0 := by
    nlinarith
  have eq5 : y * (y - 5) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq5) with hy6 hy7
  · -- Case y = 0, which is impossible
    exfalso
    exact hy1 (by linarith)
  · -- Case y - 5 = 0, so y = 5
    have hy8 : y = 5 := by linarith
    rw [hy8] at eq3
    nlinarith