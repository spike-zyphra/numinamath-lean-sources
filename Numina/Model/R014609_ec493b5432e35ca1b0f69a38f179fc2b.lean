import Mathlib

def f (x y : ℝ) := x + 2 * y + 3

theorem algebra_303698 {a b : ℝ} (ha : f (f (a^3) (a^2)) a = b) (hb : f (a^3) (f (a^2) a) = b) :
    a + b = 21 / 8 := by 
  simp [f] at ha hb
  have eq1 : a ^ 3 + 2 * a ^ 2 + 2 * a + 6 = b := by
    linarith
  have eq2 : a ^ 3 + 2 * a ^ 2 + 4 * a + 9 = b := by
    linarith
  -- Now, we have two expressions for b, so we can set them equal to each other
  have eq3 : a ^ 3 + 2 * a ^ 2 + 2 * a + 6 = a ^ 3 + 2 * a ^ 2 + 4 * a + 9 := by
    linarith [eq1, eq2]
  -- Now, from eq3, solve for a
  have ha2 : a = -3 / 2 := by
    linarith
  -- Now substitute a = -3/2 into eq1 to solve for b
  have hb2 : b = 33 / 8 := by
    rw [ha2] at eq1
    linarith 
  -- Now that we have a and b, compute a + b
  rw [ha2, hb2]
  all_goals norm_num