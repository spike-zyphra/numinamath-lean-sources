import Mathlib

theorem algebra_207638 {a b : ℝ} (f : ℝ → ℝ → ℝ) (hf : ∀ x y : ℝ, f x y = x + 2 * y + 3) (ha : f (f (a ^ 3) (a ^ 2)) a = b)
    (hb : f (a ^ 3) (f (a ^ 2) a) = b) :
    a + b = 21 / 8 := by
  have eq1 : f (a ^ 3) (a ^ 2) = a ^ 3 + 2 * a ^ 2 + 3 := by
    rw [hf]
  have eq2 : f (f (a ^ 3) (a ^ 2)) a = a ^ 3 + 2 * a ^ 2 + 2 * a + 6 := by
    rw [eq1]
    rw [hf]
    ring
  have eq3 : b = a ^ 3 + 2 * a ^ 2 + 2 * a + 6 := by 
    linarith [ha, eq2]
  have eq4 : f (a ^ 2) a = a ^ 2 + 2 * a + 3 := by 
    rw [hf]
  have eq5 : f (a ^ 3) (f (a ^ 2) a) = a ^ 3 + 2 * a ^ 2 + 4 * a + 9 := by
    rw [eq4]
    rw [hf]
    ring
  have eq6 : b = a ^ 3 + 2 * a ^ 2 + 4 * a + 9 := by
    linarith [hb, eq5]
  have eq7 : a = -3 / 2 := by 
    nlinarith [eq3, eq6]
  have eq8 : b = 33 / 8 := by 
    rw [eq3]
    rw [eq7]
    norm_num
  rw [eq7, eq8]
  all_goals norm_num