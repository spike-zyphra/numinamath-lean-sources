import Mathlib

theorem algebra_6700 (n : ℕ) (hn : n > 2) (a : Fin n → ℝ)
    (ha : (∑ i : Fin n, a i) / n = 20) (h : ((∑ i : Fin n, a i) + 27 + 53 + 40) / (n + 3) = 20 + 3) :
    n = 17 := by
  have h1 : (n : ℝ) > (2 : ℝ) := by
    exact_mod_cast (show n > 2 by linarith)
  have eq1 : (∑ i : Fin n, a i) = (20 * (n : ℝ)) := by
    have : (n : ℝ) > (0 : ℝ) := by
      nlinarith
    field_simp at ha ⊢
    linarith
  have eq2 : ((∑ i : Fin n, a i) + 27 + 53 + 40) = (20 + 3) * ((n + 3) : ℝ) := by
    have : ((n + 3) : ℝ) > (0 : ℝ) := by
      have h2 : (n : ℝ) > (2 : ℝ) := by
        exact_mod_cast (show n > 2 by linarith)
      nlinarith
    field_simp at h ⊢
    nlinarith
  rw [eq1] at eq2
  have eq3 : (n : ℝ) = 17 := by
    nlinarith
  have hn17 : n = 17 := by
    exact_mod_cast eq3
  exact hn17