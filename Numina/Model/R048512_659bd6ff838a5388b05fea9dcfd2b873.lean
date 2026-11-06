import Mathlib

theorem algebra_7644 {r b : ℕ} (hr : r = (1 / 3 : ℚ) * (r + b)) (hb : b ≠ 0)
    (h : b - 345 = (1 / 3 : ℚ) * (r + b - 345)) :
    r = 230 := by
  have h1 : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have h_eq1 : (b : ℚ) = 2 * (r : ℚ) := by
    linarith
  have h_eq2 : (r : ℚ) = 230 := by
    have h_subst : (b : ℚ) = 2 * (r : ℚ) := h_eq1
    have eq1 : ( (b : ℚ) - (345 : ℚ) ) = (1 / 3 : ℚ) * ( (r : ℚ) + (b : ℚ) - (345 : ℚ) ) := by
      linarith [h]
    rw [h_subst] at eq1
    linarith 
  exact_mod_cast h_eq2