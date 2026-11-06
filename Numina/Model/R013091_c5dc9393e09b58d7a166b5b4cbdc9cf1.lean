import Mathlib

theorem number_theory_74443 {a : ℕ → ℤ} (ha01 : a 0 = 1 ∧ a 1 = 1)
    (han : ∀ n, a (n + 1) = 14 * a n - a (n - 1)) :
    ∀ n, IsSquare (2 * a n - 1) := by
  have h1 := han 0
  have h2 := han 1
  have ha0 : a 0 = 1 := ha01.1
  have ha1 : a 1 = 1 := ha01.2
  have eq1 : a 1 = 14 * a 0 - a (0 - 1) := by 
    simpa using h1
  have eq2 : a (0 - 1) = a 0 := by
    simp
  have eq3 : a 1 = 13 * a 0 := by 
    rw [eq2] at eq1
    linarith
  have eq4 : a 1 = 13 := by
    rw [eq3, ha0]
    all_goals norm_num
  linarith [ha1, eq4]