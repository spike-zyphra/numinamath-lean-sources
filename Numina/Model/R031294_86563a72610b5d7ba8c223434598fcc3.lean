import Mathlib

theorem algebra_229271 {n : ℕ} (hn : n ≥ 3) (a b c : ℝ)
    (ha : a = (n - 2) * b) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a + b = (25 / 100) * (a + b + c)) (h2 : b + c = (60 / 100) * (a + b + c)) :
    n = 6 := by 
  have eq1 : c = 3 * a + 3 * b := by
    linarith
  have eq2 : 2 * b + 2 * c = 3 * a := by
    linarith
  rw [eq1] at eq2
  have eq3 : 8 * b = -3 * a := by
    linarith
  have eq4 : 8 = -3 * ((n - 2) : ℝ) := by
    have eq5 : a = (n - 2) * b := by
      linarith [ha]
    rw [show a = (n - 2) * b by linarith [ha]] at eq3
    apply (mul_left_inj' hb).mp
    linarith
  have eq5 : (↑n - 2 : ℝ) = (-8 / 3 : ℝ) := by
    nlinarith 
  have h5 : (↑n - 2 : ℝ) < (0 : ℝ) := by 
    linarith [eq5]
  have h5' : (↑n : ℝ) < (2 : ℝ) := by 
    nlinarith 
  have h6 : n ≥ 3 := by 
    linarith 
  have h7 : (↑n : ℝ) ≥ (3 : ℝ) := by 
    exact_mod_cast h6 
  nlinarith