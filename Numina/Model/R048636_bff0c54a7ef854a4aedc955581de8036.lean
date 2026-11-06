import Mathlib

theorem algebra_228331 {a x0 : ℝ} (ha : a ≠ 0) (h1 : 3 * x0 + 2 * x0 = 15 * a) (h2 : 1 / a * x0 + x0 = 9) :
    x0 = 6 ∧ a = 2 := by
  -- From the first equation: 3 * x0 + 2 * x0 = 15 * a, we get 5 * x0 = 15 * a, hence x0 = 3 * a
  have eq1 : x0 = 3 * a := by
    linarith
  
  -- Substitute x0 = 3 * a into the second equation: 1/a * x0 + x0 = 9
  rw [eq1] at h2
  
  -- Simplify the equation: 1/a * (3 * a) + (3 * a) = 9
  -- This simplifies to: 3 + 3 * a = 9 (since a ≠ 0)
  have eq2 : 3 + 3 * a = 9 := by 
    field_simp [ha] at h2
    linarith
  
  -- From 3 + 3 * a = 9, we solve for a:
  -- 3 * a = 6, so a = 2
  have ha2 : a = 2 := by
    linarith
  
  -- Now that we know a = 2, substitute back to get x0
  have hx0 : x0 = 6 := by
    rw [ha2] at eq1
    linarith
  
  -- The solution is x0 = 6 and a = 2
  exact ⟨hx0, ha2⟩