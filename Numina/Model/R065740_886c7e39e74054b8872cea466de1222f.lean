import Mathlib

theorem algebra_166482 (x y : ℝ) (h₀ : 0 ≤ x + y) (h₁ : 0 ≤ 2 * x + y + 2)
    (h₂ : Real.sqrt (x + y) + Real.sqrt (2 * x + y + 2) = 7) (h₃ : 3 * x + 2 * y = 23) :
    (x, y) = (-9, 25) ∨ (x, y) = (5, 4) := by
  set a := Real.sqrt (x + y) with ha
  set b := Real.sqrt (2 * x + y + 2) with hb
  have ha2 : a^2 = x + y := by
    rw [ha]
    rw [Real.sq_sqrt h₀]
  have hb2 : b^2 = 2 * x + y + 2 := by
    rw [hb]
    rw [Real.sq_sqrt h₁]
  have h2 : a + b = 7 := by 
    exact_mod_cast h₂
  have eq1 : a^2 + b^2 = 25 := by
    nlinarith
  have eq2 : a * b = 12 := by
    nlinarith
  have h4 : (a - 3) * (a - 4) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h4) with ha3 ha4
  · -- Case a = 3, so b = 4
    have ha3' : a = 3 := by linarith
    have hb4' : b = 4 := by
      nlinarith
    have hxy1 : x + y = 9 := by
      nlinarith [ha2, ha3']
    have hxy2 : 2 * x + y + 2 = 16 := by 
      nlinarith [hb2, hb4']
    have hx : x = 5 := by 
      nlinarith [hxy1, hxy2]
    have hy : y = 4 := by 
      linarith [hxy1, hx]
    right
    simp [hx, hy]
  · -- Case a = 4, so b = 3
    have ha4' : a = 4 := by linarith
    have hb3' : b = 3 := by
      nlinarith
    have hxy1 : x + y = 16 := by 
      nlinarith [ha2, ha4']
    have hxy2 : 2 * x + y + 2 = 9 := by 
      nlinarith [hb2, hb3']
    have hx : x = -9 := by 
      nlinarith [hxy1, hxy2]
    have hy : y = 25 := by 
      linarith [hxy1, hx]
    left 
    simp [hx, hy]