import Mathlib

theorem algebra_104664 {b c : ℝ} (h : ∃! x, x^2 + b * x + c = 0) (m n : ℝ)
    (hA : m^2 + b * m + c = n) (hB : (m - 8)^2 + b * (m - 8) + c = n) :
    n = 16 := by
  rcases h with ⟨x, ⟨hx, h1⟩⟩
  have h2 : ∀ y, y ^ 2 + b * y + c = 0 → y = x := by 
    intro y hy
    apply h1
    exact hy
  have h3 := h2 (-b - x) (by
    nlinarith [show x ^ 2 + b * x + c = 0 from hx]
  )
  have h4 : b = -2 * x := by
    nlinarith
  have h5 : c = x^2 := by
    rw [h4] at hx
    nlinarith
  have eq1 : m ^ 2 + b * m + c = n := by linarith
  have eq2 : (m - 8) ^ 2 + b * (m - 8) + c = n := by linarith
  have eq3 : m ^ 2 + b * m + c = (m - 8) ^ 2 + b * (m - 8) + c := by
    linarith [eq1, eq2]
  have eq4 : m ^ 2 + b * m = (m - 8) ^ 2 + b * (m - 8) := by
    nlinarith [eq3]
  have eq5 : 16 * m + 8 * b = 64 := by
    nlinarith
  have eq6 : m = x + 4 := by
    nlinarith [h4, eq5]
  have eq7 : n = 16 := by
    have eq8 : n = m ^ 2 + b * m + c := by linarith [hA]
    rw [eq8]
    rw [show b = -2 * x by linarith [h4], show c = x ^ 2 by linarith [h5]]
    rw [show m = x + 4 by linarith [eq6]]
    nlinarith
  exact_mod_cast eq7