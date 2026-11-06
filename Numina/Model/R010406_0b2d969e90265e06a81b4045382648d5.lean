import Mathlib

theorem algebra_11730 (x : ℕ) (hx : x > 0) (h : (20 * (18 + 2) + 2 * x : ℝ) / (20 + x) = 14) :
    x = 10 := by 
  have h1 : (20 * (18 + 2) + 2 * x : ℝ) / (20 + (x : ℝ)) = 14 := by
    exact_mod_cast h
  have h2 : (20 * (18 + 2) + 2 * (x : ℝ)) = 14 * (20 + (x : ℝ)) := by
    have hx1 : (x : ℝ) > (0 : ℝ) := by exact_mod_cast hx
    field_simp [(show 20 + (x : ℝ) ≠ 0 by
      nlinarith
    )] at h1 ⊢
    linarith
  have h3 : (x : ℝ) = 10 := by 
    linarith
  exact_mod_cast h3