import Mathlib

theorem algebra_114231 {r b : ℕ} (hr : r > 0) (hb : b > 0)
    (h1 : (r + b) * (1 / 3 : ℚ) = r) (h2 : (r + b + 4) * (1 / 4 : ℚ) = r) :
    r + b = 12 := by 
  have eq1 : (b : ℚ) = 2 * (r : ℚ) := by 
    have h1' : (r + b : ℚ) * (1 / 3 : ℚ) = (r : ℚ) := by
      linarith [h1]
    have h1'' : (r + b : ℚ) = 3 * (r : ℚ) := by
      linarith [h1']
    linarith [h1'']
  have eq2 : (b + 4 : ℚ) = 3 * (r : ℚ) := by
    have h2' : (r + b + 4 : ℚ) * (1 / 4 : ℚ) = (r : ℚ) := by
      linarith [h2]
    have h2'' : (r + b + 4 : ℚ) = 4 * (r : ℚ) := by
      linarith [h2']
    linarith
  have eq3 : (r : ℚ) = 4 := by 
    linarith [eq1, eq2]
  have eq4 : (b : ℚ) = 8 := by 
    rw [eq3] at eq1
    linarith
  have hr4 : r = 4 := by 
    exact_mod_cast eq3
  have hb8 : b = 8 := by 
    exact_mod_cast eq4 
  omega