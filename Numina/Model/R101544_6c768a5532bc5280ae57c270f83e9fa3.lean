import Mathlib

theorem algebra_63048 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^2 + b^2 + c^2 = 989) (h2 : (a + b)^2 + (b + c)^2 + (c + a)^2 = 2013) :
    a + b + c = 32 := by
  have h3 : (a + b)^2 + (b + c)^2 + (c + a)^2 = 2 * (a^2 + b^2 + c^2 + (a * b + b * c + c * a)) := by
    ring
  rw [h3] at h2
  have h4 : 2 * (a^2 + b^2 + c^2 + (a * b + b * c + c * a)) = 2013 := by linarith
  have h5 : a^2 + b^2 + c^2 + (a * b + b * c + c * a) = 2013 / 2 := by
    linarith
  rw [h1] at h5
  have h6 : a * b + b * c + c * a = 35 / 2 := by linarith
  have h7 : (a + b + c)^2 = 1024 := by
    calc
      (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by ring
      _ = 989 + 2 * (35 / 2) := by
        rw [h1, h6]
      _ = 1024 := by norm_num
  have h8 : a + b + c = 32 := by 
    nlinarith [show 0 < a + b + c by positivity]
  exact h8