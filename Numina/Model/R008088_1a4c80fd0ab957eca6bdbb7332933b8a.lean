import Mathlib

theorem algebra_9419 (x y : ℝ) (h1 : x - y = 0) (h2 : x ^ 2 + y = 2) :
(x = 1 ∧ y = 1) ∨ (x = -2 ∧ y = -2) := by 
  have hy : y = x := by 
    linarith 
  rw [hy] at h2 
  have h3 : x ^ 2 + x - 2 = 0 := by 
    linarith 
  have h4 : (x - 1) * (x + 2) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp h4) with h5 h6 
  · 
    left 
    have hx : x = 1 := by linarith 
    have hy1 : y = 1 := by 
      rw [hx] at hy 
      linarith 
    exact ⟨hx, hy1⟩ 
  · 
    right 
    have hx : x = -2 := by linarith 
    have hy2 : y = -2 := by 
      rw [hx] at hy 
      linarith 
    exact ⟨hx, hy2⟩