import Mathlib

/-
Find all ordered pairs of real numbers $(x, y)$ such that $x^{2} y=3$ and $x+x y=4$.
-/
theorem algebra_608894  (x y : ℝ) (h: x^2 * y = 3) (h': x + x*y = 4) : ((x= 1) ∧ (y = 3)) ∨ ((x= 3) ∧ (y = 1/3)) := by
  -- We begin with times h' by x
  have h'x: x^2 + x^2*y = 4*x := by
    calc
      _ = x*(x + x*y) := by ring_nf
      _ = x*4 := by rw[h']
      _ = _  := by ring
  
  -- Use h to cancle the x^y term and get a equation of x
  rw [h] at h'x
  
  -- Solve the equation
  have hx0: (x-3)*(x-1) = 0 := by
    calc
      _ = x^2 + 3 - 4*x := by ring
      _ = 0 := by linarith
  
  simp at hx0

  -- Case the x = 1 and x = 3
  rcases hx0 with hl | hr

  -- When x = 1, y = 3/x^2 = 1/3
  have _1: x = 3 := by linarith
  have hy: y = 1/3 := by
    calc
      _ = x^2*y / x^2 := by
        have : x^2 > 0 := by norm_num; linarith
        field_simp
      _ = 3/x^2 := by rw[h]
      _ = 3/3^2 := by rw [_1]
      _ = _ := by ring
  have : (x=3)∧(y=1/3) := by tauto
  tauto
  
  -- When x = 1, y = 3/x^2 = 3
  have _2: x = 1 := by linarith
  have hy: y = 3 := by
    calc
      _ = x^2*y / x^2 := by
        have : x^2 > 0 := by norm_num; linarith
        field_simp
      _ = 3/x^2 := by rw[h]
      _ = 3/1^2 := by rw [_2]
      _ = _ := by ring
  have : (x=1)∧(y=3) := by tauto
  tauto
