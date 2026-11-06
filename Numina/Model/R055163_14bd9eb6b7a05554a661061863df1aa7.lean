import Mathlib

theorem algebra_237858 {x y : ℤ} (hy : y ≠ 0) (h : x + y = 95) (h' : (x / y : ℚ) = 7 / 12) :
    x / y = 35 / 60 := by
  have h1 : (x : ℚ) + (y : ℚ) = 95 := by
    exact_mod_cast h
  have h2 : (x : ℚ) * 12 = (y : ℚ) * 7 := by
    have hne : (y : ℚ) ≠ 0 := by
      exact_mod_cast show (y : ℚ) ≠ 0 by exact_mod_cast hy
    field_simp [hne] at h' ⊢
    nlinarith
  have h3 : x * 12 = y * 7 := by
    exact_mod_cast h2
  have eq1 : y = 60 := by
    omega
  have eq2 : x = 35 := by
    omega
  have : x / y = 35 / 60 := by 
    rw [eq1, eq2]
    all_goals omega
  exact this