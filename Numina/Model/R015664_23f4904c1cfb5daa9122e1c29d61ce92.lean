import Mathlib

theorem algebra_241557 {a b : ℕ} (ha : a + b = 30) (hb : b + 5 = 30)
    (h1 : (a * 48 + b * 60) / (a + b) = 60) (h2 : (a * 2 + b * 60) / (a + b) = 60) :
    10 * (a * 2 + b * 60) / (a + b) = 672 := by 
  have hb2 : b = 25 := by
    omega
  have ha2 : a = 5 := by
    omega
  rw [ha2, hb2] at h1 h2
  norm_num at h1 h2
  all_goals
    omega