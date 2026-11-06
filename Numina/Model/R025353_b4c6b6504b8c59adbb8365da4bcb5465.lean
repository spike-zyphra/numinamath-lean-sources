import Mathlib

theorem algebra_271793 {a b : ℝ} (x : ℕ → ℝ) (h : ∀ n, x (n + 1) = x n - x (n - 1)) (hx1 : x 1 = a) (hx2 : x 2 = b) :
    x 100 = -a ∧ ∑ i in Finset.range 100, x (i + 1) = 2 * b - a := by
  have h01 : x 1 = 0 := by
    have eq1 : x 1 = x 0 - x (0 - 1 : ℕ) := by
      specialize h 0
      simpa using h
    have eq2 : (0 - 1 : ℕ) = 0 := by 
      omega
    rw [eq2] at eq1
    linarith
  have ha : a = 0 := by
    linarith [hx1, h01]
  have h100 : x 100 = -a := by
    rw [show a = (0 : ℝ) by linarith [ha]]
    have eq3 : x 0 = -b := by
      have eq4 : x 2 = x 1 - x 0 := by 
        specialize h 1 
        simpa using h 
      rw [show x 2 = b by linarith [hx2], show x 1 = 0 by linarith [h01]] at eq4
      linarith
    norm_num [h, h01, eq3]
  have h8 : ∑ i in Finset.range 100, x (i + 1) = 2 * b - a := by
    rw [show a = (0 : ℝ) by linarith [ha]]
    have eq3 : x 1 = 0 := by linarith [h01]
    have eq2 : x 0 = -b := by
      have eq4 : x 2 = x 1 - x 0 := by 
        specialize h 1 
        simpa using h 
      rw [show x 2 = b by linarith [hx2], show x 1 = 0 by linarith [h01]] at eq4
      linarith
    norm_num [Finset.sum_range_succ, h, eq3, eq2]
    all_goals
      linarith 
  constructor
  · exact h100
  · exact h8