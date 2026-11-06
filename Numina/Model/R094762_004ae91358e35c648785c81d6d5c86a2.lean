import Mathlib

theorem algebra_63838 {r y g : ℕ} (h₀ : r + y + g = 28) (h₁ : r = (1 / 2 : ℚ) * (r + y)) (h₂ : r = (1 / 3 : ℚ) * (g + r)) :
    r = 7 := by
  have eq1 : (r : ℚ) + (y : ℚ) + (g : ℚ) = (28 : ℚ) := by 
    exact_mod_cast h₀
  have eq2 : (r : ℚ) = (1 / 2 : ℚ) * ((r : ℚ) + (y : ℚ)) := by 
    exact_mod_cast h₁
  have hy : (y : ℚ) = (r : ℚ) := by 
    linarith
  have eq3 : (r : ℚ) = (1 / 3 : ℚ) * ((g : ℚ) + (r : ℚ)) := by 
    exact_mod_cast h₂
  have hg : (g : ℚ) = 2 * (r : ℚ) := by 
    linarith
  have hr : (r : ℚ) = 7 := by 
    have h : (r : ℚ) + (y : ℚ) + (g : ℚ) = (28 : ℚ) := by 
      exact_mod_cast h₀
    rw [show (y : ℚ) = (r : ℚ) by exact_mod_cast hy, show (g : ℚ) = 2 * (r : ℚ) by exact_mod_cast hg] at h
    linarith
  exact_mod_cast hr