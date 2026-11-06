import Mathlib

theorem inequalities_63738 {a b c : ℝ} (ha : abs a ≥ abs (b + c)) (hb : abs b ≥ abs (c + a)) (hc : abs c ≥ abs (a + b)) :
    a + b + c = 0 := by 
  have h₁ : a^2 ≥ (b + c)^2 := by 
    apply sq_le_sq.mpr 
    exact ha 
  have h₂ : b^2 ≥ (c + a)^2 := by 
    apply sq_le_sq.mpr 
    exact hb 
  have h₃ : c^2 ≥ (a + b)^2 := by 
    apply sq_le_sq.mpr 
    exact hc 
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]