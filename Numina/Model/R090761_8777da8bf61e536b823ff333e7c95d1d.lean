import Mathlib

theorem algebra_237493 {x y : ℝ} (h1 : 3*x^2+x*y-2*y^2=-5) (h2 : x^2+2*x*y+y^2=1) :
    (x=3/5 ∧ y=-8/5) ∨ (x=-3/5 ∧ y=8/5) := by 
  have h3 : (x + y) ^ 2 = 1 := by linarith 
  have h4 : (x + y = 1) ∨ (x + y = -1) := by 
    rw [sq_eq_one_iff] at h3 
    exact h3 
  cases h4 with 
  | inl hxy1 =>
    have hy1 : y = 1 - x := by linarith 
    rw [hy1] at h1 
    have hx1 : x = -3 / 5 := by 
      nlinarith 
    have hy2 : y = 8 / 5 := by 
      rw [hx1] at hy1 
      linarith 
    right 
    exact ⟨by linarith, by linarith⟩ 
  | inr hxy2 =>
    have hy1 : y = -1 - x := by linarith 
    rw [hy1] at h1 
    have hx1 : x = 3 / 5 := by 
      nlinarith 
    have hy2 : y = -8 / 5 := by 
      rw [hx1] at hy1 
      linarith 
    left 
    exact ⟨by linarith, by linarith⟩