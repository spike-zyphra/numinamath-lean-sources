import Mathlib

theorem algebra_235947 (n : ℕ) (h : n > 0) (x : ℝ) (hx : x ≠ 0)
    (h1 : (n * x + 89) / (n + 1) = 91) (h2 : (n * x + 64) / (n + 1) = 86) :
    n = 4 := by
  have eq1 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast h
  have eq2 : (n + 1 : ℝ) > (0 : ℝ) := by
    have hn : (n : ℝ) > (0 : ℝ) := eq1
    nlinarith
  have eq3 : (n * x + 89 : ℝ) = 91 * ((n + 1) : ℝ) := by
    have h1' : (n + 1 : ℝ) ≠ 0 := by linarith
    field_simp at h1 ⊢
    linarith
  have eq4 : (n * x + 64 : ℝ) = 86 * ((n + 1) : ℝ) := by
    have h2' : (n + 1 : ℝ) ≠ 0 := by linarith
    field_simp at h2 ⊢
    linarith
  have eq5 : (n : ℝ) * x - 91 * (n : ℝ) - 2 = 0 := by
    nlinarith
  have eq6 : (n : ℝ) * x - 86 * (n : ℝ) - 22 = 0 := by
    nlinarith
  have eq7 : (n : ℝ) = 4 := by
    nlinarith
  have hn : n = 4 := by
    exact_mod_cast eq7
  exact hn